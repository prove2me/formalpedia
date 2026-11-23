-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mul_col_of_unit
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.mul_col_of_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:55.03022+00:00
-- url     : https://prove2.me/theorems/a9d91b01-a174-4554-954b-46701adec4ff
-- title:
--   Chi: mul col of unit
-- statement:
--   The Chi construction uses the mul col of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L158-L164

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.mul_col_of_unit {M O : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {p : Fin g ⊕ Fin g}
    (h : ∀ r, M r p = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r p) (q : Fin g ⊕ Fin g) :
    (O * M) q p = O q p := by sorry
