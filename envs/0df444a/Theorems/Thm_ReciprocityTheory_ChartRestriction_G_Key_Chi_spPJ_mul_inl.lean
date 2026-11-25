-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spPJ_mul_inl
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.spPJ_mul_inl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:42.583131+00:00
-- url     : https://prove2.me/theorems/01958828-2527-4b8e-9c85-3e211d375f77
-- title:
--   Chi: sp PJ mul inl
-- statement:
--   The Chi construction uses the sp PJ mul inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L94-L104

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.spPJ_mul_inl (j : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g)
    (p : Fin g ⊕ Fin g) :
    (spPJ j * M) (Sum.inl i) p = if i = j then M (Sum.inr j) p else M (Sum.inl i) p := by sorry
