-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_continuous_weightFunction
-- name    : ReciprocityTheory.L2DbarEstimates.I.continuous_weightFunction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:12.8958+00:00
-- url     : https://prove2.me/theorems/66d878db-a9c9-41a8-814c-c9b4d35093ea
-- title:
--   I: continuous weight Function
-- statement:
--   The I construction uses the continuous weight Function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L27-L35

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.continuous_weightFunction {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) : Continuous (ev n g ph r) := by sorry
