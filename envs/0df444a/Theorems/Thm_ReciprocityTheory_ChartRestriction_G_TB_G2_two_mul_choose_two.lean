-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_two_mul_choose_two
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.two_mul_choose_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:09.542334+00:00
-- url     : https://prove2.me/theorems/4d1edf30-dff2-4329-8b57-613fd951dc6d
-- title:
--   G2: two mul choose two
-- statement:
--   The G2 construction uses the two mul choose two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L88-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by sorry
