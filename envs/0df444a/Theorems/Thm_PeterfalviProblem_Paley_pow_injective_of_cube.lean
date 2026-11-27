-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_pow_injective_of_cube
-- name    : PeterfalviProblem.Paley.pow_injective_of_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:58:51.71121+00:00
-- url     : https://prove2.me/theorems/db52d8f5-3987-5b7a-bec1-19284c51b399
-- title:
--   Paley: pow injective of cube
-- statement:
--   If `z^{E³} = z` for all `z`, then `z ↦ z^E` is injective.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L302-L305
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L302-L305

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.pow_injective_of_cube (hcube : ∀ z : F, z ^ (E * E * E) = z) {x y : F}
    (h : x ^ E = y ^ E) : x = y := by sorry
