-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterElementaryUnit_commute_of_nonadjacent
-- name    : SoficGroups.finiteOuterElementaryUnit_commute_of_nonadjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/ec1b6b6c-4e15-49cf-ba0f-0d16a7964b32
-- title:
--   SoficGroups.finiteOuterElementaryUnit_commute_of_nonadjacent
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R]

theorem SoficGroups.finiteOuterElementaryUnit_commute_of_nonadjacent
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute (elementaryUnit i j hij A) (elementaryUnit k l hkl B) := by sorry
