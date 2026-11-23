-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:30.977126+00:00
-- url     : https://prove2.me/theorems/ddd8823d-cfa5-4440-9fdb-903bc75d0c4c
-- title:
--   Local Maximum Second Derivative: levi V re eq
-- statement:
--   The Local Maximum Second Derivative construction uses the levi V re eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L142-L156

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (f y : ℂ)) x ξ).re * 4 =
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k)))
          (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k))) +
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k))
          (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k)) := by sorry
