-- Prove2me | Theorems.Thm_SoficGroups_finite_finiteOuterBlockRootSubgroup
-- name    : SoficGroups.finite_finiteOuterBlockRootSubgroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/b97ad6da-a8d6-4e4c-8903-463ba224eacf
-- title:
--   SoficGroups.finite_finiteOuterBlockRootSubgroup
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem SoficGroups.finite_finiteOuterBlockRootSubgroup
    (W : Submodule (ZMod 2) R) [Finite W]
    (i j : Fin 3) (hij : i ≠ j) :
    Finite (finiteOuterBlockRootSubgroup W i j hij) := by sorry
