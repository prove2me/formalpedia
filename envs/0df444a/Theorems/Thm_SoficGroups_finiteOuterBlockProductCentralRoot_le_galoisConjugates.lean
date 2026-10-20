-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_le_galoisConjugates
-- name    : SoficGroups.finiteOuterBlockProductCentralRoot_le_galoisConjugates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/67fafda7-8067-4bc8-bc75-35511952890d
-- title:
--   SoficGroups.finiteOuterBlockProductCentralRoot_le_galoisConjugates
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem SoficGroups.finiteOuterBlockProductCentralRoot_le_galoisConjugates
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) (hst : s ≠ t) :
    finiteOuterBlockProductCentralRootSubgroup W i k hik B ≤
      finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B s ⊔
        finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B t := by sorry
