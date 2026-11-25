-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_rk_mul_inl
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_rk_mul_inl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:33.609876+00:00
-- url     : https://prove2.me/theorems/09866b40-2c15-51ce-98fc-b3a597aa3ec9
-- title:
--   Chi: sp Diag rk mul inl
-- statement:
--   The Chi construction uses the sp Diag rk mul inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L154-L162

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_rk_mul_inl (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inl i) p = M (Sum.inl i) p + u i * ∑ l, v l * M (Sum.inl l) p := by sorry
