-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:29:26.621502+00:00
-- url     : https://prove2.me/theorems/d900bc1b-1bed-4539-b127-5fbf544fb395
-- title:
--   Tanner Lifted Product: lps Original Filled Chart Meromorphic polynomial
-- statement:
--   Actual chartwise meromorphy is preserved by any complex polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L235-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L235-L256

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (P : Polynomial ℂ) :
    lpsOriginalFilledChartMeromorphic N hN (fun x => P.eval (F x)) := by sorry
