-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_integral_wvol
-- name    : ReciprocityTheory.L2DbarEstimates.F.gm_integral_wvol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:02.826394+00:00
-- url     : https://prove2.me/theorems/27dfc27b-efc6-5d36-b76c-1d5bd287ca09
-- title:
--   F: gm integral wvol
-- statement:
--   The F construction uses the gm integral wvol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L292-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L292-L307

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
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
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

theorem ReciprocityTheory.L2DbarEstimates.F.gm_integral_wvol (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : Measurable ph)
    (G : M → ℂ) :
    ∫ x, G x ∂wvol n z ph = ∫ x, (Real.exp (-ph x) : ℂ) * G x ∂vol n z ∧
      (Integrable G (wvol n z ph) → Integrable (fun x => (Real.exp (-ph x) : ℂ) * G x) (vol n z)) := by sorry
