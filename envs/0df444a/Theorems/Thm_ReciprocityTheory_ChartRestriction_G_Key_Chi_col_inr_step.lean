-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_col_inr_step
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.col_inr_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:55.645391+00:00
-- url     : https://prove2.me/theorems/3210f6a7-3464-40d9-aeb0-36ff07e47927
-- title:
--   Chi: col inr step
-- statement:
--   The Chi construction uses the col inr step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenMain.lean#L9-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenMain.lean#L9-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.col_inr_step (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M)
    (hk : ∀ r, M r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) :
    ∃ O ∈ spH g, ColsFixed k O ∧
      (∀ r, O r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) ∧
      ∀ r, (O * M) r (Sum.inr k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr k) := by sorry
