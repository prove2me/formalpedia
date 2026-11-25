-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_nonpos_of_isLocalMax
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:22.749257+00:00
-- url     : https://prove2.me/theorems/a0ac3e73-9406-44df-8399-c6f6210c7e81
-- title:
--   Local Maximum Second Derivative: levi V re nonpos of is Local Max
-- statement:
--   The Local Maximum Second Derivative construction uses the levi V re nonpos of is Local Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L158-L165

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

theorem ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (ξ : Fin n → ℂ) : (leviV n (fun y => (f y : ℂ)) x ξ).re ≤ 0 := by sorry
