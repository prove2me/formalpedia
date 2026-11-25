-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sign_col
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.sign_col
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:03.203872+00:00
-- url     : https://prove2.me/theorems/7a908f6a-4b0a-4975-99db-95a242c3aa3c
-- title:
--   Chi: sign col
-- statement:
--   The Chi construction uses the sign col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L145-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L145-L169

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.sign_col (k : Fin g) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl k then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by sorry
