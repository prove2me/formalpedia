-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_phase2
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.phase2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:37.54082+00:00
-- url     : https://prove2.me/theorems/f358a94c-a9c6-5b6d-a887-19ad9c385fda
-- title:
--   Chi: phase2
-- statement:
--   The Chi construction uses the phase2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L27-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenFin.lean#L27-L112

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.phase2 (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    (∀ j, M (Sum.inr j) (Sum.inl k) = 0) → ∑ j, (M (Sum.inl j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ (∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0) ∧
      ∀ i j, (O * M) (Sum.inl i) (Sum.inl k) ≠ 0 → (O * M) (Sum.inl j) (Sum.inl k) ≠ 0 → i = j := by sorry
