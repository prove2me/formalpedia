-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiffConj_add_one
-- name    : PeterfalviProblem.Paley.powDiffConj_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T04:58:55.93448+00:00
-- url     : https://prove2.me/theorems/b6fb9ea5-5c43-5ba5-a8af-83ce17c95edb
-- title:
--   Paley: pow Diff Conj add one
-- statement:
--   The Paley construction uses the pow Diff Conj add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L323-L329
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L323-L329

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiffConj_add_one (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiffConj E a + 1 = (a + 1) ^ E * (powDiff E a)⁻¹ := by sorry
