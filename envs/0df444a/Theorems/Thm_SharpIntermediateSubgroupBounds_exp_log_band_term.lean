-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_exp_log_band_term
-- name    : SharpIntermediateSubgroupBounds.exp_log_band_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:23.121113+00:00
-- url     : https://prove2.me/theorems/31852578-526a-54b1-ad36-7f67fe77a8cb
-- title:
--   Sharp Intermediate Subgroup Bounds: exp log band term
-- statement:
--   One summand of the exact rational finite sum has precisely the
--   exponential form used in `finiteThetaSum`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L70-L87
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L70-L87

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

theorem SharpIntermediateSubgroupBounds.exp_log_band_term {q n r : ℕ} (hq : 1 < q) (hn : 0 < n) :
    Real.exp
        (Real.log (q : ℝ) * (r : ℝ) * (indexLog q n - (r : ℝ))) =
      (n : ℝ) ^ r / (q : ℝ) ^ (r * r) := by sorry
