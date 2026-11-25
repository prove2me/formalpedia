-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_fromBlocks_mul_inr
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.fromBlocks_mul_inr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:53.551843+00:00
-- url     : https://prove2.me/theorems/065f9ee9-b00c-5e3c-a39d-72e46134a470
-- title:
--   Chi: from Blocks mul inr
-- statement:
--   The Chi construction uses the from Blocks mul inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L151-L156

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.fromBlocks_mul_inr (A B C D : Matrix (Fin g) (Fin g) ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (fromBlocks A B C D * M) (Sum.inr i) p =
      (∑ j, C i j * M (Sum.inl j) p) + ∑ j, D i j * M (Sum.inr j) p := by sorry
