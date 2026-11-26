-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_cast_eq_qFactorial_div
-- name    : SharpIntermediateSubgroupBounds.qBinom_cast_eq_qFactorial_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:53:58.789776+00:00
-- url     : https://prove2.me/theorems/41a65cfc-8130-4b1a-9898-ee5b0441d580
-- title:
--   Sharp Intermediate Subgroup Bounds: q Binom cast eq q Factorial div
-- statement:
--   The usual product formula, stated in `ℚ` to make the division exact.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L161-L171
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L161-L171

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators

theorem SharpIntermediateSubgroupBounds.qBinom_cast_eq_qFactorial_div {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℚ) =
      qFactorial q n / (qFactorial q k * qFactorial q (n - k)) := by sorry
