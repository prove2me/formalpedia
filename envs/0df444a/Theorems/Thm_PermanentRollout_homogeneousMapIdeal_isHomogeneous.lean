-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapIdeal_isHomogeneous
-- name    : PermanentRollout.homogeneousMapIdeal_isHomogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/71651411-3a21-4b01-a1f5-40198e5892f1
-- title:
--   PermanentRollout.homogeneousMapIdeal_isHomogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMapIdeal_isHomogeneous
    {ι : Type*} (F : ι → MvPolynomial ι ℂ) (e : ℕ)
    (hF : ∀ i, (F i).IsHomogeneous e) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ)
      (homogeneousMapIdeal F) := by sorry
