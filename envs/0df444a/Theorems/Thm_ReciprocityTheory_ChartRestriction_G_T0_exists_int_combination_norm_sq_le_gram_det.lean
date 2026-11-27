-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_int_combination_norm_sq_le_gram_det
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exists_int_combination_norm_sq_le_gram_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:48.731336+00:00
-- url     : https://prove2.me/theorems/b84b23e7-3497-49b3-9f23-cd061f02ae61
-- title:
--   T0: exists int combination norm sq le gram det
-- statement:
--   The T0 construction uses the exists int combination norm sq le gram det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L7-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L7-L89

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

theorem ReciprocityTheory.ChartRestriction.G.T0.exists_int_combination_norm_sq_le_gram_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (u : Fin N → E) (hu : LinearIndependent ℝ u) :
    ∃ y : Fin N → ℤ, y ≠ 0 ∧ ‖∑ i, y i • u i‖ ^ 2 ≤ N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by sorry
