-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_continuous_two_form_norm_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_norm_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:36.72331+00:00
-- url     : https://prove2.me/theorems/68c2c7ae-af15-5951-aec5-2b8cf3d03d36
-- title:
--   F: continuous two form norm sq
-- statement:
--   The F construction uses the continuous two form norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L209-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L209-L214

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_norm_sq (n : ℕ) : Continuous (sq2 n) := by sorry
