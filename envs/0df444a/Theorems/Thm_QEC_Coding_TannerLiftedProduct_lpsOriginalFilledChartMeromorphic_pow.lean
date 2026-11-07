-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:30:13.419066+00:00
-- url     : https://prove2.me/theorems/28d83f83-b512-40e4-8980-13c000be7d83
-- title:
--   Tanner Lifted Product: lps Original Filled Chart Meromorphic pow
-- statement:
--   Actual chartwise meromorphy is closed under natural powers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L222-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L222-L230

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_pow
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (m : ℕ) :
    lpsOriginalFilledChartMeromorphic N hN (F^m) := by sorry
