-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_universal_rpow
-- name    : SharpIntermediateSubgroupBounds.interval_card_lt_universal_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:47.178814+00:00
-- url     : https://prove2.me/theorems/6a6e4d5e-55b7-44ab-b081-552628363aa4
-- title:
--   Sharp Intermediate Subgroup Bounds: interval card lt universal rpow
-- statement:
--   Universal bound in the literal `n ^ ((log_2 n)/4)` notation.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L185-L189
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L185-L189

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

theorem SharpIntermediateSubgroupBounds.interval_card_lt_universal_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant 2 * (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by sorry
