-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_exists_paley_collision_pow_mul
-- name    : PeterfalviProblem.Paley.exists_paley_collision_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:57.475966+00:00
-- url     : https://prove2.me/theorems/b98fa1bf-b340-5d85-b077-368cad13cbf1
-- title:
--   Paley: exists paley collision pow mul
-- statement:
--   Two distinct points of `T` with the same value of `powDiff E` give two distinct points of `T`
--   with the same value of `powDiff (E²)`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L414-L437
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L414-L437

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.exists_paley_collision_pow_mul [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3)
    (hE : Odd E) (hcube : ∀ z : F, z ^ (E * E * E) = z) {a b : F} (ha : a ∈ paleySet F)
    (hb : b ∈ paleySet F) (hab : a ≠ b) (hval : powDiff E a = powDiff E b) :
    ∃ c ∈ paleySet F, ∃ d ∈ paleySet F, c ≠ d ∧ powDiff (E * E) c = powDiff (E * E) d := by sorry
