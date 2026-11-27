-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiffConjNeg_add_one
-- name    : PeterfalviProblem.Paley.powDiffConjNeg_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T04:59:03.317339+00:00
-- url     : https://prove2.me/theorems/98377212-471e-5ad1-88dd-73057f621547
-- title:
--   Paley: pow Diff Conj Neg add one
-- statement:
--   The Paley construction uses the pow Diff Conj Neg add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L331-L337
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L331-L337

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiffConjNeg_add_one (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiffConjNeg E a + 1 = -a ^ E * (powDiff E a)⁻¹ := by sorry
