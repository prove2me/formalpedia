-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSMatrixProductMachine_entryMatrix_product_fields
-- name    : QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine.entryMatrix_product_fields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:19:32.626337+00:00
-- url     : https://prove2.me/theorems/2f838240-9e72-4259-9494-69e0adde38fc
-- title:
--   LPSMatrix Product Machine: entry Matrix product fields
-- statement:
--   Exact original LPS entry-matrix product, with unchanged coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMatrixProductMachine.lean#L63-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMatrixProductMachine.lean#L63-L69

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine.entryMatrix_product_fields (q:ℕ) (hq:0<q) (a b c d e f g h:Fin q) :
    fields q (lpsEntryMatrix q a b c d*lpsEntryMatrix q e f g h)=
      [(a.val*e.val+b.val*g.val)%q,(a.val*f.val+b.val*h.val)%q,
       (c.val*e.val+d.val*g.val)%q,(c.val*f.val+d.val*h.val)%q] := by sorry
