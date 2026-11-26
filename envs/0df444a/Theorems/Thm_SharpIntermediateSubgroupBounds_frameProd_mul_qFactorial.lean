-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_mul_qFactorial
-- name    : SharpIntermediateSubgroupBounds.frameProd_mul_qFactorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:43:01.966677+00:00
-- url     : https://prove2.me/theorems/8cb93e4a-2ff4-49b8-a4b2-87215d4ffe20
-- title:
--   Sharp Intermediate Subgroup Bounds: frame Prod mul q Factorial
-- statement:
--   Clearing the denominator in the ordered-frame product formula.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L279-L296
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L279-L296

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

theorem SharpIntermediateSubgroupBounds.frameProd_mul_qFactorial {q n k : ℕ} (hk : k ≤ n) :
    frameProd q n k * qFactorial q (n - k) =
      framePower q k * qFactorial q n := by sorry
