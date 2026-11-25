-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_deriv_deriv_nonpos_of_isLocalMax
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.deriv_deriv_nonpos_of_isLocalMax
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:44.46882+00:00
-- url     : https://prove2.me/theorems/6b896255-50aa-46d1-94d4-9878c7cb52b7
-- title:
--   Local Maximum Second Derivative: deriv deriv nonpos of is Local Max
-- statement:
--   The Local Maximum Second Derivative construction uses the deriv deriv nonpos of is Local Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L11-L43

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

theorem ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} (hmax : IsLocalMax g 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) : deriv (deriv g) 0 ≤ 0 := by sorry
