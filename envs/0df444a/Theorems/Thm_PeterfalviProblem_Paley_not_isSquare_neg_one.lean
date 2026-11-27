-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_not_isSquare_neg_one
-- name    : PeterfalviProblem.Paley.not_isSquare_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:59:05.529655+00:00
-- url     : https://prove2.me/theorems/0cf76bb6-3c82-455c-9b15-5f26189065e2
-- title:
--   Paley: not is Square neg one
-- statement:
--   `-1` is not a square when `|F| ≡ 3 (mod 4)`. By Euler's criterion, a square `a` satisfies
--   `a^{(|F|-1)/2} = 1`, but here the exponent is odd.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L55-L66
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L55-L66

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]

theorem PeterfalviProblem.Paley.not_isSquare_neg_one [Fintype F] (h2 : ringChar F ≠ 2) (h4 : Fintype.card F % 4 = 3) :
    ¬ IsSquare (-1 : F) := by sorry
