-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_leastPrime
-- name    : SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:33.95918+00:00
-- url     : https://prove2.me/theorems/0d237259-5260-5471-b946-8999df2861a3
-- title:
--   Sharp Intermediate Subgroup Bounds: interval card lt least Prime
-- statement:
--   The least-prime-divisor form of the manuscript's main finite-group
--   theorem.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L147-L152
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L147-L152

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

theorem SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (H.index.minFac : ℝ) *
        sharpScale H.index.minFac H.index := by sorry
