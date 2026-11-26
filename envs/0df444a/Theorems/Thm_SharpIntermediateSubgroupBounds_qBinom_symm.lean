-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_symm
-- name    : SharpIntermediateSubgroupBounds.qBinom_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:52.704568+00:00
-- url     : https://prove2.me/theorems/d6b93d0c-988a-422b-b4ba-d5e6ce483446
-- title:
--   Sharp Intermediate Subgroup Bounds: q Binom symm
-- statement:
--   Symmetry of Gaussian binomial coefficients.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L146-L158
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L146-L158

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

theorem SharpIntermediateSubgroupBounds.qBinom_symm {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k = qBinom q n (n - k) := by sorry
