-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:28.518829+00:00
-- url     : https://prove2.me/theorems/e1938d3e-14cb-4aaf-a151-b37c6cee5ea6
-- title:
--   T0: exists ne zero mem norm sq le gram det div rel Index
-- statement:
--   The T0 construction uses the exists ne zero mem norm sq le gram det div rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L95-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L95-L271

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule Matrix

theorem ReciprocityTheory.ChartRestriction.G.T0.exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (w : Fin N → E) (hw : LinearIndependent ℝ w) (Λ : AddSubgroup E)
    (hΛ : ∀ i, w i ∈ Λ) (hI : (span ℤ (Set.range w)).toAddSubgroup.relIndex Λ ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ ^ 2 ≤ N * ((gram ℝ w).det /
      ((span ℤ (Set.range w)).toAddSubgroup.relIndex Λ : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by sorry
