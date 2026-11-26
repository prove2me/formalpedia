-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_leastPrime_rpow
-- name    : SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:43.959791+00:00
-- url     : https://prove2.me/theorems/e7f08b1a-5be7-4400-a85d-7132cb670934
-- title:
--   Sharp Intermediate Subgroup Bounds: interval card lt least Prime rpow
-- statement:
--   Least-prime bound in the literal real-power notation of Theorem 1.1.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L155-L162
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L155-L162

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

theorem SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (H.index.minFac : ℝ) *
        (H.index : ℝ) ^
          (indexLog H.index.minFac H.index / 4) := by sorry
