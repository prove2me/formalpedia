-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_sum_splits_evalTwo_word
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalTwo_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:32.166796+00:00
-- url     : https://prove2.me/theorems/f6ae9d3e-b6ab-4c63-b5c3-74833e284620
-- title:
--   G2: sum splits eval Two word
-- statement:
--   The G2 construction uses the sum splits eval Two word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L133-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SumSplitsEvalTwoWord.lean#L133-L208

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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalTwo_word (c : ι → ι → k) (hc : ∀ x y, c x y = c y x) (Ls : List ι) (hnd : Ls.Nodup)
    (m : ι →₀ ℕ) (φ : List ι → k) :
    2 * ((splits (word Ls m)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
        φ (word Ls (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum := by sorry
