-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_move_col
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.move_col
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:45.819046+00:00
-- url     : https://prove2.me/theorems/0522a7f8-1e98-40fc-be7a-96a24b1b955f
-- title:
--   Chi: move col
-- statement:
--   The Chi construction uses the move col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L114-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L114-L143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.move_col (k j : Fin g) (hjk : (k : ℕ) ≤ j) (hne : j ≠ k) (s : ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl j then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r, (O * M) r (Sum.inl k) = if r = Sum.inl k then s else 0 := by sorry
