-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_isSquare_or_isSquare_neg
-- name    : PeterfalviProblem.Paley.isSquare_or_isSquare_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:58:49.906073+00:00
-- url     : https://prove2.me/theorems/a9375145-805e-5030-941a-17420efbfe92
-- title:
--   Paley: is Square or is Square neg
-- statement:
--   When `|F| ≡ 3 (mod 4)`, every nonzero element is a square or minus a square.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L69-L76
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L69-L76

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]

theorem PeterfalviProblem.Paley.isSquare_or_isSquare_neg [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) {a : F} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by sorry
