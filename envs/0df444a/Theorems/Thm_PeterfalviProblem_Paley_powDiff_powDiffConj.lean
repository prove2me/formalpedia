-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiff_powDiffConj
-- name    : PeterfalviProblem.Paley.powDiff_powDiffConj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:32.674198+00:00
-- url     : https://prove2.me/theorems/82057710-7b5d-5373-91e9-a75cd70ecdc8
-- title:
--   Paley: pow Diff pow Diff Conj
-- statement:
--   `powDiff (E²) (powDiffConj E a) = (powDiff E a)⁻¹^{E²}`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L345-L349
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L345-L349

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiff_powDiffConj (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiff (E * E) (powDiffConj E a) = (powDiff E a)⁻¹ ^ (E * E) := by sorry
