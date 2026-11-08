-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSMatrixProductMachine_fields_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine.fields_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:59:13.48565+00:00
-- url     : https://prove2.me/theorems/ed2273b0-3dba-4e0d-9f0e-60ae1e429762
-- title:
--   LPSMatrix Product Machine: fields injective
-- statement:
--   Proved actual execution phase or mathematical tape invariant for the complete program.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMatrixProductMachine.lean#L72-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMatrixProductMachine.lean#L72-L77

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine.fields_injective (q:ℕ) (hq:0<q) : Function.Injective (fields q) := by sorry
