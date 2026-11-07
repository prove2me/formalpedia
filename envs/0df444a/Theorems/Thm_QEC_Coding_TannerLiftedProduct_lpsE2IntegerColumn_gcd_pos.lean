-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2IntegerColumn_gcd_pos
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2IntegerColumn_gcd_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:05.385444+00:00
-- url     : https://prove2.me/theorems/06baf2a8-ac93-47e0-af27-5272b56052dc
-- title:
--   Tanner Lifted Product: lps E2 Integer Column gcd pos
-- statement:
--   A positive genuine determinant excludes an all-zero first column and proves gcd positivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L121-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L121-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2IntegerColumn_gcd_pos (M : GL (Fin 2) ℝ) (hd : 0<M.det.val)
    (a c : ℤ) (t : ℝ) (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t) :
    0<Int.gcd a c := by sorry
