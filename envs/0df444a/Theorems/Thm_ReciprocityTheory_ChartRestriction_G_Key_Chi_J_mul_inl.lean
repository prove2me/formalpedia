-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_J_mul_inl
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.J_mul_inl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:36.5036+00:00
-- url     : https://prove2.me/theorems/f8a07ac7-8ee9-51bb-bd4c-332611bd9cc0
-- title:
--   Chi: J mul inl
-- statement:
--   The Chi construction uses the J mul inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L66-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.J_mul_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g) (q : Fin g ⊕ Fin g) :
    (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by sorry
