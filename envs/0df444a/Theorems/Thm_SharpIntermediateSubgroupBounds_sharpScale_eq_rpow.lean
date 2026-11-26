-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_sharpScale_eq_rpow
-- name    : SharpIntermediateSubgroupBounds.sharpScale_eq_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:35.632002+00:00
-- url     : https://prove2.me/theorems/d4e5607a-d3f0-4c27-9b9d-3556ef8f052f
-- title:
--   Sharp Intermediate Subgroup Bounds: sharp Scale eq rpow
-- statement:
--   The exponential scale agrees exactly with the conventional real-power
--   notation in the manuscript.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L136-L143
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L136-L143

import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]

theorem SharpIntermediateSubgroupBounds.sharpScale_eq_rpow {q n : ℕ} (hq : 1 < q) (hn : 0 < n) :
    sharpScale q n = (n : ℝ) ^ (indexLog q n / 4) := by sorry
