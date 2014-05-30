#![allow(unused_must_use)]

extern crate debug;
extern crate syntax;
extern crate rustc;
extern crate collections;

use collections::HashSet;
use std::cell::RefCell;
use std::fmt;
use std::io::MemWriter;
use std::os;
use std::str;

use rustc::driver::config;
use rustc::driver::driver;
use rustc::driver::session;
use rustc::metadata::creader::Loader;
use rustc::middle::lint;
use rustc::middle::privacy;
use rustc::middle::ty;
use syntax::abi;
use syntax::ast;
use syntax::codemap::{CodeMap, Span};
use syntax::diagnostic;
use syntax::parse::token;
use syntax::visit::Visitor;
use syntax::visit;

struct V {
    exported_items: privacy::ExportedItems,
    tcx: ty::ctxt,
    types_needed: RefCell<HashSet<ast::DefId>>,
}

struct CType<'a, T>(&'a T, &'a V);

fn main() {
    let args = os::args();
    let file = Path::new(args.get(1).as_slice());

    let input = driver::FileInput(file.clone());

    // Configure our session
    let sessopts = config::Options {
        maybe_sysroot: {
            use std::io::Command;
            let out = Command::new("which").arg("rustc").output().unwrap();
            let path = Path::new(out.output.as_slice());
            Some(path.dir_path().dir_path())
        },
        crate_types: vec!(config::CrateTypeRlib),
        lint_opts: vec!((lint::Warnings, lint::Allow)),
        ..config::basic_options().clone()
    };

    // Build the session
    let diagnostic_handler = diagnostic::default_handler(diagnostic::Auto);
    let span_diagnostic_handler =
        diagnostic::mk_span_handler(diagnostic_handler, CodeMap::new());
    let sess = session::build_session_(sessopts,
                                       Some(file.clone()),
                                       span_diagnostic_handler);
    let cfg = config::build_configuration(&sess);

    // Run the compiler
    let krate = driver::phase_1_parse_input(&sess, cfg, &input);
    let (krate, ast_map) = driver::phase_2_configure_and_expand(
                                &sess, &mut Loader::new(&sess), krate,
                                &from_str("foo").unwrap());
    let driver::CrateAnalysis {
        exported_items, ty_cx, ..
    } = driver::phase_3_run_analysis_passes(sess, &krate, ast_map);

    // Crawl the crate
    let mut out = MemWriter::new();
    let mut v = V {
        exported_items: exported_items,
        tcx: ty_cx,
        types_needed: RefCell::new(HashSet::new()),
    };
    visit::walk_crate(&mut (&mut v, &mut out as &mut Writer), &krate, ());

    println!(r"
\#include <stdint.h>
\#include <stdbool.h>

typedef struct RustString \{
    char *data;
    unsigned long len;
\} RustString;
");

    for did in v.types_needed.borrow().iter() {
        v.print_type(*did);
    }
    println!("{}", str::from_utf8(out.get_ref()).unwrap());
}

impl<'a, 'b> Visitor<()> for (&'a mut V, &'a mut Writer) {
    fn visit_fn(&mut self, fk: &visit::FnKind, fd: &ast::FnDecl,
                b: &ast::Block, s: Span, _: ast::NodeId, _: ()) {
        match *fk {
            visit::FkItemFn(name, _, _, abi::C) => {
                let (ref mut v, ref mut out) = *self;
                let name = token::get_ident(name);
                write!(*out, "{} {}(", CType(&*fd.output, *v), name.get());
                for (i, arg) in fd.inputs.iter().enumerate() {
                    if i != 0 { write!(*out, ", "); }

                    let name = match arg.pat.node {
                        ast::PatIdent(_, ref path, _) => {
                            token::get_ident(path.segments.get(0).identifier)
                                  .get().to_string()
                        }
                        _ => format!("arg{}", i),
                    };

                    write!(*out, "{} {}", CType(&*arg.ty, *v), name);
                }
                writeln!(*out, ");");
            }
            _ => {}
        }
        visit::walk_fn(self, fk, fd, b, s, ())
    }
}

impl<'a> fmt::Show for CType<'a, ast::Ty> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use rustc::middle::typeck::astconv::{ast_ty_to_ty, AstConv};
        use rustc::middle::typeck::infer;
        use std::rc::Rc;

        impl AstConv for V {
            fn tcx<'a>(&'a self) -> &'a ty::ctxt { &self.tcx }
            fn get_item_ty(&self, id: ast::DefId) -> ty::ty_param_bounds_and_ty {
                ty::lookup_item_type(&self.tcx, id)
            }
            fn get_trait_def(&self, id: ast::DefId) -> Rc<ty::TraitDef> {
                ty::lookup_trait_def(&self.tcx, id)
            }
            fn ty_infer(&self, _span: Span) -> ty::t {
                infer::new_infer_ctxt(&self.tcx).next_ty_var()
            }
        }

        let CType(inner, v) = *self;

        let t_t = ast_ty_to_ty(v, &infer::new_infer_ctxt(&v.tcx), inner);
        write!(f, "{}", CType(&t_t, v))
    }
}

impl<'a> fmt::Show for CType<'a, ast::IntTy> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CType(inner, _) = *self;
        write!(f, "{}", match *inner {
            ast::TyI8 => "char",
            ast::TyI16 => "short",
            ast::TyI32 => "int",
            ast::TyI64 => "int64_t",
            ast::TyI => "long int",
        })
    }
}

impl<'a> fmt::Show for CType<'a, ast::UintTy> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CType(inner, _) = *self;
        write!(f, "{}", match *inner {
            ast::TyU8 => "unsigned char",
            ast::TyU16 => "unsigned short",
            ast::TyU32 => "unsigned",
            ast::TyU64 => "uint64_t",
            ast::TyU => "unsigned long",
        })
    }
}

impl<'a> fmt::Show for CType<'a, ast::FloatTy> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CType(inner, _) = *self;
        write!(f, "{}", match *inner {
            ast::TyF32 => "float",
            ast::TyF64 => "double",
            ast::TyF128 => "__float128",
        })
    }
}

impl<'a> fmt::Show for CType<'a, ty::t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CType(inner, v) = *self;
        match ty::get(*inner).sty {
            ty::ty_nil | ty::ty_bot => write!(f, "void"),
            ty::ty_bool => write!(f, "bool"),
            ty::ty_char => write!(f, "int"),
            ty::ty_int(i) => write!(f, "{}", CType(&i, v)),
            ty::ty_uint(u) => write!(f, "{}", CType(&u, v)),
            ty::ty_float(t) => write!(f, "{}", CType(&t, v)),

            ty::ty_box(t) |
            ty::ty_ptr(ty::mt { ty: t, .. }) |
            ty::ty_rptr(_, ty::mt { ty: t, .. }) |
            ty::ty_uniq(t) => {
                match ty::get(t).sty {
                    ty::ty_str => write!(f, "RustString"),
                    _ => write!(f, "{}*", CType(&t, v)),
                }
            }
            ty::ty_struct(did, _) => {
                match v.types_needed.try_borrow_mut() {
                    Some(mut set) => { set.insert(did); }
                    None => {}
                }
                write!(f, "struct {}", v.path_name(did))
            }

            ty::ty_enum(..) |
            ty::ty_vec(..) |
            ty::ty_bare_fn(..) |
            ty::ty_closure(..) |
            ty::ty_trait(..) |
            ty::ty_tup(..) => fail!("unimplemented"),

            ty::ty_str => fail!("impossible?"),
            ty::ty_param(..) => fail!("generic struct in FFI?"),
            ty::ty_self(..) => fail!("self in FFI?"),

            ty::ty_infer(..) | ty::ty_err => unreachable!(),
        }
    }
}

impl V {
    fn print_type(&self, did: ast::DefId) {
        let ty = ty::lookup_item_type(&self.tcx, did);
        match ty::get(ty.ty).sty {
            ty::ty_struct(_, ref s) => {
                println!("typedef struct {} \\{", self.path_name(did));
                for field in ty::struct_fields(&self.tcx, did, s).iter() {
                    println!("    {} {};",
                             CType(&field.mt.ty, self),
                             token::get_ident(field.ident).get());
                }
                println!("\\} {}_t;\n", self.path_name(did));
            }
            _ => fail!("unimplemented type"),
        }
    }

    fn path_name(&self, did: ast::DefId) -> String {
        ty::with_path(&self.tcx, did, |mut elems| {
            token::get_name(elems.last().unwrap().name())
                  .get().to_string()
        })
    }
}
