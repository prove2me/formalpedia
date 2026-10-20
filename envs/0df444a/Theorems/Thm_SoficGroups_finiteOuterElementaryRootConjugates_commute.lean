-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterElementaryRootConjugates_commute
-- name    : SoficGroups.finiteOuterElementaryRootConjugates_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/c07a1b6c-f55f-4835-b7d5-ed60a4d3a15e
-- title:
--   SoficGroups.finiteOuterElementaryRootConjugates_commute
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

theorem SoficGroups.finiteOuterElementaryRootConjugates_commute
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A C P Q : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd P))
        (elementaryRootHom i j hij (Multiplicative.ofAdd A)))
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd Q))
        (elementaryRootHom i j hij (Multiplicative.ofAdd C))) := by sorry
