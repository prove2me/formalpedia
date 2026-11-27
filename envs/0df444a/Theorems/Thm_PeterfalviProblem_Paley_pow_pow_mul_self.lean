-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_pow_pow_mul_self
-- name    : PeterfalviProblem.Paley.pow_pow_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:58:45.238169+00:00
-- url     : https://prove2.me/theorems/7b915076-fc31-43aa-b5db-dc8953460ab2
-- title:
--   Paley: pow pow mul self
-- statement:
--   If `z^{E³} = z` for all `z`, then `(z^E)^{E²} = z`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L296-L299
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L296-L299

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}

theorem PeterfalviProblem.Paley.pow_pow_mul_self (hcube : ∀ z : F, z ^ (E * E * E) = z) (z : F) :
    (z ^ E) ^ (E * E) = z := by sorry
