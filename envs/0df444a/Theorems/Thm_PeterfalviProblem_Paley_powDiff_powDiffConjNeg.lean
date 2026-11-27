-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiff_powDiffConjNeg
-- name    : PeterfalviProblem.Paley.powDiff_powDiffConjNeg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:59.500395+00:00
-- url     : https://prove2.me/theorems/84668722-82af-4cd1-b198-a9ead9e63f7e
-- title:
--   Paley: pow Diff pow Diff Conj Neg
-- statement:
--   `powDiff (E²) (powDiffConjNeg E a) = (powDiff E a)⁻¹^{E²}`, the same value as for
--   `powDiffConj`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L353-L361
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L353-L361

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiff_powDiffConjNeg (hE : Odd E) (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiff (E * E) (powDiffConjNeg E a) = (powDiff E a)⁻¹ ^ (E * E) := by sorry
