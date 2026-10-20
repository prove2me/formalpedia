-- Prove2me | Theorems.Thm_PermanentRollout_criticalGradientIdeal_isHomogeneous
-- name    : PermanentRollout.criticalGradientIdeal_isHomogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/6e720e6a-5364-4b76-811c-7135242982e2
-- title:
--   PermanentRollout.criticalGradientIdeal_isHomogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.criticalGradientIdeal_isHomogeneous {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (hP : P.IsHomogeneous d) :
    (homogeneousMapIdeal
      (fun i : Fin m => MvPolynomial.pderiv i P)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) := by sorry
