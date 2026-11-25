-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_col_single_entry
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.col_single_entry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:42.570005+00:00
-- url     : https://prove2.me/theorems/45185e0f-78b5-54ef-959f-1824db037cab
-- title:
--   Chi: col single entry
-- statement:
--   The Chi construction uses the col single entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L70-L73

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.col_single_entry {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by sorry
