-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDelta_cusp_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDelta_cusp_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:32:06.9647+00:00
-- url     : https://prove2.me/theorems/e7035dc4-5a3b-4a81-937f-133ace47c96b
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Delta cusp coefficient
-- statement:
--   Actual integer widths and local pole orders give an analytic Delta-cleared cusp coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L121-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L121-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDelta_cusp_coefficient
    (f : ℂ → ℂ) (n m k : ℕ) (hm : 0 < m) (hnk : n ≤ m*k)
    (hf : AnalyticAt ℂ (fun q => q^n * f q) 0)
    (α : ℂ) (hα : α ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ q : ℂ, H q = (q^m * lpsOriginalMeromorphicDeltaQCoefficient (q^m))^k * f (α*q) := by sorry
