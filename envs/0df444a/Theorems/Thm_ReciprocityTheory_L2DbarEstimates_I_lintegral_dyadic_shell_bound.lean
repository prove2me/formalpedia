-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_lintegral_dyadic_shell_bound
-- name    : ReciprocityTheory.L2DbarEstimates.I.lintegral_dyadic_shell_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:56.792844+00:00
-- url     : https://prove2.me/theorems/f2dba5e0-af69-4a34-a2a5-2d95df0c1215
-- title:
--   I: lintegral dyadic shell bound
-- statement:
--   The I construction uses the lintegral dyadic shell bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L105-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L105-L192

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

theorem ReciprocityTheory.L2DbarEstimates.I.lintegral_dyadic_shell_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (e : α → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (U : Set α) (hU : MeasurableSet U) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (hn : 1 ≤ n) (ε B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hZ : μ (U ∩ {x | e x ≤ 0}) = 0)
    (hsh : ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in U ∩ {x | t ^ 2 / 2 ≤ e x ∧ e x ≤ t ^ 2},
        ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (2 * B * ε ^ 2) := by sorry
