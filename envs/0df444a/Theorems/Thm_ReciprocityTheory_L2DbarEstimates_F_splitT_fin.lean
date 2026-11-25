-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_fin
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_fin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:12.377115+00:00
-- url     : https://prove2.me/theorems/8d463767-1c1d-516c-9bf2-fff3fa0df0b4
-- title:
--   F: split T fin
-- statement:
--   The F construction uses the split T fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L29-L44

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
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

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_fin (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by sorry
