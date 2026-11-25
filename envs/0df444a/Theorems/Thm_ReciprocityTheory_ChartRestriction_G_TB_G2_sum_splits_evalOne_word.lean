-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_sum_splits_evalOne_word
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalOne_word
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:12.032824+00:00
-- url     : https://prove2.me/theorems/0e5c0c9c-78e0-5e7a-95d5-328d4e37b843
-- title:
--   G2: sum splits eval One word
-- statement:
--   The G2 construction uses the sum splits eval One word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L61-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L61-L86

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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalOne_word (g : ι → k) (Ls : List ι) (hnd : Ls.Nodup) (m : ι →₀ ℕ) (φ : List ι → k) :
    ((splits (word Ls m)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      (Ls.map (fun y => (m y : k) * g y * φ (word Ls (m - Finsupp.single y 1)))).sum := by sorry
