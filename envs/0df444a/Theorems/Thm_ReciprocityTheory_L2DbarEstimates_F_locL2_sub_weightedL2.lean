-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_sub_weightedL2
-- name    : ReciprocityTheory.L2DbarEstimates.F.locL2_sub_weightedL2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:48.415797+00:00
-- url     : https://prove2.me/theorems/7fc76f43-8169-57f9-9391-919e11536a59
-- title:
--   F: loc L2 sub weighted L2
-- statement:
--   The F construction uses the loc L2 sub weighted L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L506-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L506-L576

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.F.locL2_sub_weightedL2 (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (F0 : M → ℂ) (hF0 : Continuous F0) (u : Lp ℂ 2 (wvol n z ph)) :
    LocalL2Isometry (vol n z) (fun x => F0 x - u x) := by sorry
