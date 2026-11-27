-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_eq_or_of_sub_inv_sq_eq
-- name    : PeterfalviProblem.Paley.eq_or_of_sub_inv_sq_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:04:39.70172+00:00
-- url     : https://prove2.me/theorems/60d4d86a-8ee2-5d0b-87b8-0852742c1a3d
-- title:
--   Paley: eq or of sub inv sq eq
-- statement:
--   If `(u - u⁻¹)² = (w - w⁻¹)²`, then `u` is one of `w`, `-w`, `w⁻¹` and `-w⁻¹`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L105-L141
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L105-L141

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]

theorem PeterfalviProblem.Paley.eq_or_of_sub_inv_sq_eq {u w : Fˣ}
    (h : ((u : F) - (u : F)⁻¹) ^ 2 = ((w : F) - (w : F)⁻¹) ^ 2) :
    u = w ∨ u = -w ∨ u = w⁻¹ ∨ u = -w⁻¹ := by sorry
