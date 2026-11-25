-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sSup_image_le_max
-- name    : ReciprocityTheory.L2DbarEstimates.F.sSup_image_le_max
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:29.445792+00:00
-- url     : https://prove2.me/theorems/76fc5cf7-4597-454b-abbc-4a5f4c6f4d83
-- title:
--   F: s Sup image le max
-- statement:
--   The F construction uses the s Sup image le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Choice.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Choice.lean#L24-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Choice
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

theorem ReciprocityTheory.L2DbarEstimates.F.sSup_image_le_max {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by sorry
