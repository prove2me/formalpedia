-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_integrable
-- name    : ReciprocityTheory.L2DbarEstimates.F.uwr_integrable
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:12.360117+00:00
-- url     : https://prove2.me/theorems/b1822cbb-4a63-471b-acb9-21fd41c1aad2
-- title:
--   F: uwr integrable
-- statement:
--   The F construction uses the uwr integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L103-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L103-L125

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

theorem ReciprocityTheory.L2DbarEstimates.F.uwr_integrable (hz : IsLocalHomeomorph z) (u h : M → ℂ) (p : M → ℝ) (hp : Continuous p)
    (hu : AEStronglyMeasurable u (vol n z))
    (hfin : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x => u x * h x) (vol n z) := by sorry
