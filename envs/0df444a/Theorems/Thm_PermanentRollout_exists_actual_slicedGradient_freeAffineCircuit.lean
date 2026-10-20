-- Prove2me | Theorems.Thm_PermanentRollout_exists_actual_slicedGradient_freeAffineCircuit
-- name    : PermanentRollout.exists_actual_slicedGradient_freeAffineCircuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/e4f76644-42ba-41d8-90f6-daa128a3aa64
-- title:
--   PermanentRollout.exists_actual_slicedGradient_freeAffineCircuit
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.exists_actual_slicedGradient_freeAffineCircuit
    {k m : ℕ}
    (circuit : FreeAffineCircuit (Fin m))
    (output : FreeAffineForm (Fin m))
    (houtput : output ∈ circuit.outputs)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ)) :
    ∃ D : FreeAffineCircuit (Fin k),
      D.multiplicationCount = 3 * circuit.multiplicationCount ∧
      D.polynomials = (Finset.univ : Finset (Fin k)).toList.map
        (slicedGradientPolynomial (output.eval circuit.values) W A) := by sorry
