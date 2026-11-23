-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_inv_val
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.rkU_inv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:11.264685+00:00
-- url     : https://prove2.me/theorems/7bb45298-62bb-4eac-a52d-d82ad636e1db
-- title:
--   Chi: rk U inv val
-- statement:
--   The Chi construction uses the rk U inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L150-L152

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.rkU_inv_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    (((rkU u v h)⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) =
      1 - vecMulVec u v := by sorry
