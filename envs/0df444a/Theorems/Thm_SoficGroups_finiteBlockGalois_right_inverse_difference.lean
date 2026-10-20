-- Prove2me | Theorems.Thm_SoficGroups_finiteBlockGalois_right_inverse_difference
-- name    : SoficGroups.finiteBlockGalois_right_inverse_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/b1ad34ca-74e3-4005-95e2-f9f0692e11db
-- title:
--   SoficGroups.finiteBlockGalois_right_inverse_difference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem SoficGroups.finiteBlockGalois_right_inverse_difference
    (s t : finiteBlockGaloisField) (hst : s ≠ t)
    (C : Matrix (Fin 3) (Fin 3) R) :
    (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R t -
      (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R s = C := by sorry
