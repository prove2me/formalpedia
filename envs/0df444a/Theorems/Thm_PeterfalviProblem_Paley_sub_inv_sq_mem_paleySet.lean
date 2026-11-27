-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_sub_inv_sq_mem_paleySet
-- name    : PeterfalviProblem.Paley.sub_inv_sq_mem_paleySet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:02:22.847892+00:00
-- url     : https://prove2.me/theorems/3bfe5566-46eb-502e-a610-6345afe3e965
-- title:
--   Paley: sub inv sq mem paley Set
-- statement:
--   In characteristic three, `(u - u⁻¹)²` lies in the Paley set when `u² ≠ 1` and `-1` is not a
--   square. Indeed `(u - u⁻¹)² + 1 = (u + u⁻¹)²`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L80-L102
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L80-L102

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]

theorem PeterfalviProblem.Paley.sub_inv_sq_mem_paleySet (h30 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F)) {u : Fˣ}
    (hu : u ^ 2 ≠ 1) : ((u : F) - (u : F)⁻¹) ^ 2 ∈ paleySet F := by sorry
