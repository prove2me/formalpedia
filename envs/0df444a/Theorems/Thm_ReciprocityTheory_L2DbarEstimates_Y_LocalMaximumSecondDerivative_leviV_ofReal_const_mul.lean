-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:58.241462+00:00
-- url     : https://prove2.me/theorems/cb36f47a-e96b-4ac3-b560-eb6bb54fdd63
-- title:
--   Local Maximum Second Derivative: levi V of Real const mul
-- statement:
--   The Local Maximum Second Derivative construction uses the levi V of Real const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L190-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L190-L206

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

theorem ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul {f : V n → ℝ} {x : V n} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y : ℝ) : ℂ)) x ξ = (c : ℂ) * leviV n (fun y => (f y : ℂ)) x ξ := by sorry
