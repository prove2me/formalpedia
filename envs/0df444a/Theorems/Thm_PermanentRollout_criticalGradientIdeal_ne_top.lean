-- Prove2me | Theorems.Thm_PermanentRollout_criticalGradientIdeal_ne_top
-- name    : PermanentRollout.criticalGradientIdeal_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/fbd02cdc-cf16-4185-b842-22df68bb26c1
-- title:
--   PermanentRollout.criticalGradientIdeal_ne_top
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

theorem PermanentRollout.criticalGradientIdeal_ne_top {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d) :
    homogeneousMapIdeal
      (fun i : Fin m => MvPolynomial.pderiv i P) ≠ ⊤ := by sorry
