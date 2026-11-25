-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_snd_nonpos_of_isLocalMax
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.snd_nonpos_of_isLocalMax
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:40.306792+00:00
-- url     : https://prove2.me/theorems/c192ccdc-af34-4b67-95f1-715f21deb62f
-- title:
--   Local Maximum Second Derivative: snd nonpos of is Local Max
-- statement:
--   The Local Maximum Second Derivative construction uses the snd nonpos of is Local Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L51-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DerivDerivNonposOfIsLocalMax.lean#L51-L81

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
set_option maxHeartbeats 400000

theorem ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.snd_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (u : V n) : fderiv ℝ (fderiv ℝ f) x u u ≤ 0 := by sorry
