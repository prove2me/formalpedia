-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_conjugate_by_successor
-- name    : SoficGroups.finiteOuterElementaryRoot_conjugate_by_successor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/a3c7112c-6c55-4635-be26-685e0c187b3f
-- title:
--   SoficGroups.finiteOuterElementaryRoot_conjugate_by_successor
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

theorem SoficGroups.finiteOuterElementaryRoot_conjugate_by_successor
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    let x := elementaryRootHom i j hij (Multiplicative.ofAdd A)
    let y := elementaryRootHom j k hjk (Multiplicative.ofAdd B)
    let z := elementaryRootHom i k hik (Multiplicative.ofAdd (A * B))
    y * x * y⁻¹ = z⁻¹ * x := by sorry
