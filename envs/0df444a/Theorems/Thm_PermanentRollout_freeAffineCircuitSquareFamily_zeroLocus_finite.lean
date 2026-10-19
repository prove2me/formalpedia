-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_zeroLocus_finite
-- name    : PermanentRollout.freeAffineCircuitSquareFamily_zeroLocus_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/56d82d1b-3fcf-4dc5-9848-9c02f8bf8701
-- title:
--   PermanentRollout.freeAffineCircuitSquareFamily_zeroLocus_finite
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

theorem PermanentRollout.freeAffineCircuitSquareFamily_zeroLocus_finite
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k))
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (houtput : ∀ i, (output i).eval circuit.values = F i) :
    (MvPolynomial.zeroLocus ℂ
      (Ideal.span (Set.range
        (freeAffineCircuitSquareFamily circuit output target)))).Finite := by sorry
