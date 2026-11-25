-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_sq_le_integrable_sum
-- name    : ReciprocityTheory.L2DbarEstimates.F.locL2_of_sq_le_integrable_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:27.427799+00:00
-- url     : https://prove2.me/theorems/5c7d61fa-cce5-5ee9-8c3f-d4c40e3ca5b9
-- title:
--   F: loc L2 of sq le integrable sum
-- statement:
--   The F construction uses the loc L2 of sq le integrable sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L127-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L127-L153

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

theorem ReciprocityTheory.L2DbarEstimates.F.locL2_of_sq_le_integrable_sum {E : Type*} [NormedAddCommGroup E] (u : M → E)
    (hu : AEStronglyMeasurable u (vol n z))
    (c F1 F2 : M → ℝ) (hc : Continuous c) (hF1 : ∀ x, 0 ≤ F1 x) (hF2 : ∀ x, 0 ≤ F2 x)
    (hF1m : AEMeasurable (fun x => ENNReal.ofReal (F1 x)) (vol n z))
    (hI1 : ∫⁻ x, ENNReal.ofReal (F1 x) ∂vol n z < ⊤)
    (hI2 : ∫⁻ x, ENNReal.ofReal (F2 x) ∂vol n z < ⊤)
    (hb : ∀ x, ‖u x‖ ^ 2 ≤ c x * (F1 x + F2 x)) : LocalL2Isometry (vol n z) u := by sorry
