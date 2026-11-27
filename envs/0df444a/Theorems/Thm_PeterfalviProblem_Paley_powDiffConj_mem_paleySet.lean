-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiffConj_mem_paleySet
-- name    : PeterfalviProblem.Paley.powDiffConj_mem_paleySet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:48.747867+00:00
-- url     : https://prove2.me/theorems/c481e3f8-a11f-5de5-b7f9-f738addccc5d
-- title:
--   Paley: pow Diff Conj mem paley Set
-- statement:
--   If `a ∈ T` and `powDiff E a` is a square, then `powDiffConj E a ∈ T`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L373-L382
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L373-L382

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiffConj_mem_paleySet (hcube : ∀ z : F, z ^ (E * E * E) = z) {a : F}
    (ha : a ∈ paleySet F) (hsq : IsSquare (powDiff E a)) : powDiffConj E a ∈ paleySet F := by sorry
