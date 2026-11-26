-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_finiteU_and_sharp_leastPrime
-- name    : SharpIntermediateSubgroupBounds.finiteU_and_sharp_leastPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:13.52684+00:00
-- url     : https://prove2.me/theorems/69377b1c-07aa-5b37-8600-7733dac6448e
-- title:
--   Sharp Intermediate Subgroup Bounds: finite U and sharp least Prime
-- statement:
--   The two inequalities in the finite main theorem, packaged together:
--   first the exact rational finite sum and then its strict theta simplification.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L166-L175
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L166-L175

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

theorem SharpIntermediateSubgroupBounds.finiteU_and_sharp_leastPrime {H : Subgroup G} (hn : 1 < H.index) :
    ((Nat.card (interval H) : ℚ) ≤
        finiteUQ H.index H.index.minFac) ∧
      (Nat.card (interval H) : ℝ) <
        sharpConstant (H.index.minFac : ℝ) *
          (H.index : ℝ) ^
            (indexLog H.index.minFac H.index / 4) := by sorry
