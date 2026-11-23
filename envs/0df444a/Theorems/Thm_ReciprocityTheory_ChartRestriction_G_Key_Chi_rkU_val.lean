-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.rkU_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:27.195936+00:00
-- url     : https://prove2.me/theorems/064a1cf3-d03d-4f36-97f0-8268dd39c52c
-- title:
--   Chi: rk U val
-- statement:
--   The Chi construction uses the rk U val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L147-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L147-L148

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.rkU_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    ((rkU u v h : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) = 1 + vecMulVec u v := by sorry
