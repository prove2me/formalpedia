-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_ratCast_finiteUQ_eq_finiteThetaSum
-- name    : SharpIntermediateSubgroupBounds.ratCast_finiteUQ_eq_finiteThetaSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:28.043524+00:00
-- url     : https://prove2.me/theorems/7d1c8b33-0871-590f-9cab-06a3cd9a08b0
-- title:
--   Sharp Intermediate Subgroup Bounds: rat Cast finite UQ eq finite Theta Sum
-- statement:
--   Casting the exact finite packing sum to `ℝ` gives the analytic finite
--   theta sum, term by term.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L91-L108
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean#L91-L108

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

theorem SharpIntermediateSubgroupBounds.ratCast_finiteUQ_eq_finiteThetaSum {q n : ℕ} (hq : 1 < q)
    (hn : 0 < n) :
    ((finiteUQ n q : ℚ) : ℝ) =
      finiteThetaSum (q : ℝ) (indexLog q n) := by sorry
