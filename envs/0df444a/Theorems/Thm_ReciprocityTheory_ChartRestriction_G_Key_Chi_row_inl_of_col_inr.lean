-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_row_inl_of_col_inr
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.row_inl_of_col_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:33.098859+00:00
-- url     : https://prove2.me/theorems/7b4c5929-67d7-5c8d-ac79-32e39546a976
-- title:
--   Chi: row inl of col inr
-- statement:
--   The Chi construction uses the row inl of col inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L186-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L186-L208

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.row_inl_of_col_inr {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {i : Fin g}
    (h : ∀ r, M r (Sum.inr i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr i))
    (q : Fin g ⊕ Fin g) :
    M (Sum.inl i) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inl i) q := by sorry
