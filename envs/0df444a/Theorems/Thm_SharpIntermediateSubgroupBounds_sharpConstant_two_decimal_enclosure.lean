-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_two_decimal_enclosure
-- name    : SharpIntermediateSubgroupBounds.sharpConstant_two_decimal_enclosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:24.08978+00:00
-- url     : https://prove2.me/theorems/377db6fc-fcd8-486a-b330-b7e29acd9a7b
-- title:
--   Sharp Intermediate Subgroup Bounds: sharp Constant two decimal enclosure
-- statement:
--   Exact enclosure of the value printed in the manuscript:
--   `7.371968801461 < c(2) < 7.371968801462`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Decimal.lean#L403-L419
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Decimal.lean#L403-L419

import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
open Filter Finset Topology

theorem SharpIntermediateSubgroupBounds.sharpConstant_two_decimal_enclosure :
    (7371968801461 : ℝ) / 10 ^ 12 < sharpConstant 2 ∧
      sharpConstant 2 < (3685984400731 : ℝ) / 500000000000 := by sorry
