-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sum_eJ
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.sum_eJ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:06.286902+00:00
-- url     : https://prove2.me/theorems/fe5b02e8-0b3e-4252-9bd8-978efee527a1
-- title:
--   Chi: sum e J
-- statement:
--   The Chi construction uses the sum e J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L77-L83

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.sum_eJ (j i : Fin g) (x : Fin g → ℤ) :
    ∑ l, eJ j i l * x l = if i = j then x j else 0 := by sorry
