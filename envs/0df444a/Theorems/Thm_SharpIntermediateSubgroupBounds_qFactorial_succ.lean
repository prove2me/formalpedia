-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_succ
-- name    : SharpIntermediateSubgroupBounds.qFactorial_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:32.652381+00:00
-- url     : https://prove2.me/theorems/106d9994-4679-5e1e-b1ea-1717103f0065
-- title:
--   Sharp Intermediate Subgroup Bounds: q Factorial succ
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the q Factorial succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L71-L73
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L71-L73

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

theorem SharpIntermediateSubgroupBounds.qFactorial_succ (q n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * (q ^ (n + 1) - 1) := by sorry
