-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_isWeaklyRegular
-- name    : PermanentRollout.freeAffineCircuitSquareFamily_isWeaklyRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/c0d7a83c-8ea8-46bd-af6b-b5c3799a7c8f
-- title:
--   PermanentRollout.freeAffineCircuitSquareFamily_isWeaklyRegular
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

theorem PermanentRollout.freeAffineCircuitSquareFamily_isWeaklyRegular
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k))
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (houtput : ∀ i, (output i).eval circuit.values = F i) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ)
      (List.ofFn (freeAffineCircuitSquareFamily circuit output target)) := by sorry
