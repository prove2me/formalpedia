-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterBlockGaloisConjugatorWithCoefficient_mem
-- name    : SoficGroups.finiteOuterBlockGaloisConjugatorWithCoefficient_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/94432af2-8f9f-4716-8e36-a10eff990f8a
-- title:
--   SoficGroups.finiteOuterBlockGaloisConjugatorWithCoefficient_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem SoficGroups.finiteOuterBlockGaloisConjugatorWithCoefficient_mem
    (W : Submodule (ZMod 2) R)
    (j k : Fin 3) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t ∈
      finiteOuterBlockRootSubgroup W j k hjk := by sorry
