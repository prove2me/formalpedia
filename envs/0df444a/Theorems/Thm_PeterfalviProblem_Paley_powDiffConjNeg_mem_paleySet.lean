-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiffConjNeg_mem_paleySet
-- name    : PeterfalviProblem.Paley.powDiffConjNeg_mem_paleySet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:06:13.836654+00:00
-- url     : https://prove2.me/theorems/5d7fd252-7f58-40e6-a560-6a555ae81786
-- title:
--   Paley: pow Diff Conj Neg mem paley Set
-- statement:
--   If `a ∈ T` and `powDiff E a` is not a square, then `powDiffConjNeg E a ∈ T`. Here
--   `-powDiff E a` is a square.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L386-L410
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L386-L410

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiffConjNeg_mem_paleySet [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3)
    (hcube : ∀ z : F, z ^ (E * E * E) = z) {a : F} (ha : a ∈ paleySet F)
    (hsq : ¬ IsSquare (powDiff E a)) : powDiffConjNeg E a ∈ paleySet F := by sorry
