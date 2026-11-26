-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
-- name    : SharpIntermediateSubgroupBounds.natFloor_indexLog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:25.709687+00:00
-- url     : https://prove2.me/theorems/ba9f2ba1-8ce1-5b85-bd62-d369695591f2
-- title:
--   Sharp Intermediate Subgroup Bounds: nat Floor index Log
-- statement:
--   The natural floor of the real logarithm is Mathlib's exact natural
--   logarithm.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L42-L44
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L42-L44

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

theorem SharpIntermediateSubgroupBounds.natFloor_indexLog (q n : ℕ) :
    Nat.floor (indexLog q n) = Nat.log q n := by sorry
