-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_frameProd
-- name    : SharpIntermediateSubgroupBounds.qBinom_mul_frameProd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:46:56.267322+00:00
-- url     : https://prove2.me/theorems/07a04b64-0bfe-4b7c-aed7-b53ef2d1bdd6
-- title:
--   Sharp Intermediate Subgroup Bounds: q Binom mul frame Prod
-- statement:
--   The ordered-frame form of the Gaussian product identity.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L299-L314
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L299-L314

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

theorem SharpIntermediateSubgroupBounds.qBinom_mul_frameProd {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k * frameProd q k k = frameProd q n k := by sorry
