-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unweightBack
-- name    : ReciprocityTheory.L2DbarEstimates.F.unweightBack
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:26.281993+00:00
-- url     : https://prove2.me/theorems/862e4e32-a73a-40d8-93e9-8add0d87927d
-- title:
--   F: unweight Back
-- statement:
--   The F construction uses the unweight Back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBack.lean#L10-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBack.lean#L10-L227

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBack
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

theorem ReciprocityTheory.L2DbarEstimates.F.unweightBack (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : UnweightBackStatement n M := by sorry
