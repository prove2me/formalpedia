-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_single_isTestForm
-- name    : ReciprocityTheory.L2DbarEstimates.F.gm_single_isTestForm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:18.321419+00:00
-- url     : https://prove2.me/theorems/86848f7c-6a3d-5c51-8c6f-89d3d5674b98
-- title:
--   F: gm single is Test Form
-- statement:
--   The F construction uses the gm single is Test Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L423-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L423-L440

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

theorem ReciprocityTheory.L2DbarEstimates.F.gm_single_isTestForm (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) : IsTestForm n z (gmSingle ph φ j) := by sorry
