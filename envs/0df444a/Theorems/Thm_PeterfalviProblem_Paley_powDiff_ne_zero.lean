-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiff_ne_zero
-- name    : PeterfalviProblem.Paley.powDiff_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T04:58:37.801462+00:00
-- url     : https://prove2.me/theorems/60b945b5-9639-4cb0-a0a6-153f976a116e
-- title:
--   Paley: pow Diff ne zero
-- statement:
--   If `z^{E³} = z` for all `z`, then `powDiff E a ≠ 0`: otherwise `(a + 1)^E = a^E`, so
--   `a + 1 = a`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L309-L315
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L309-L315

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiff_ne_zero (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) : powDiff E a ≠ 0 := by sorry
