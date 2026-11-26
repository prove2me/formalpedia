-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementary_interval_bound_rpow
-- name    : SharpIntermediateSubgroupBounds.elementary_interval_bound_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:26.680349+00:00
-- url     : https://prove2.me/theorems/1970437e-2028-5bf2-b6a1-5674f0dcdd9a
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary interval bound rpow
-- statement:
--   The elementary generating-set estimate from the introduction, in its
--   literal real-power form.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L202-L218
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L202-L218

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

theorem SharpIntermediateSubgroupBounds.elementary_interval_bound_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) ≤
      (H.index : ℝ) ^ indexLog 2 H.index := by sorry
