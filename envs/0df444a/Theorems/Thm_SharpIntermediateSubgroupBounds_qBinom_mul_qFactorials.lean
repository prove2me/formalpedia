-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_qFactorials
-- name    : SharpIntermediateSubgroupBounds.qBinom_mul_qFactorials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:24.508591+00:00
-- url     : https://prove2.me/theorems/7f896b1e-dfbc-4870-8775-ce7d8aaeca0a
-- title:
--   Sharp Intermediate Subgroup Bounds: q Binom mul q Factorials
-- statement:
--   The division-free Gaussian factorial identity.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L92-L143
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L92-L143

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

theorem SharpIntermediateSubgroupBounds.qBinom_mul_qFactorials {q : ℕ} (hq : 2 ≤ q) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n := by sorry
