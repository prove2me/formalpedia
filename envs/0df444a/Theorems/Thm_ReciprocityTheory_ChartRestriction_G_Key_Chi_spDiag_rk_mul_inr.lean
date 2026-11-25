-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_rk_mul_inr
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_rk_mul_inr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:05.760478+00:00
-- url     : https://prove2.me/theorems/fed5700f-60a4-50c4-a71d-b0493c7d910b
-- title:
--   Chi: sp Diag rk mul inr
-- statement:
--   The Chi construction uses the sp Diag rk mul inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L164-L172

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_rk_mul_inr (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inr i) p = M (Sum.inr i) p - v i * ∑ l, u l * M (Sum.inr l) p := by sorry
