-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_powDiff_pow_mul_pow_mul
-- name    : PeterfalviProblem.Paley.powDiff_pow_mul_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:08:20.65306+00:00
-- url     : https://prove2.me/theorems/72f94312-368f-4d1e-ad1b-0ada75b5e795
-- title:
--   Paley: pow Diff pow mul pow mul
-- statement:
--   `powDiff (E⁴) = powDiff E`, because `z^{E⁴} = z^E` when `z^{E³} = z`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L440-L447
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L440-L447

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.powDiff_pow_mul_pow_mul (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiff ((E * E) * (E * E)) a = powDiff E a := by sorry
