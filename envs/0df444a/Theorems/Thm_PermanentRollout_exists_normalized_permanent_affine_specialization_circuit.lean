-- Prove2me | Theorems.Thm_PermanentRollout_exists_normalized_permanent_affine_specialization_circuit
-- name    : PermanentRollout.exists_normalized_permanent_affine_specialization_circuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/b0b946c5-8b88-4472-9b1f-e0517d84870b
-- title:
--   PermanentRollout.exists_normalized_permanent_affine_specialization_circuit
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

theorem PermanentRollout.exists_normalized_permanent_affine_specialization_circuit
    {n m : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (substitution : (Fin n × Fin n) → FreeAffineInput (Fin m))
    (P : MvPolynomial (Fin m) ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hspecialization :
      MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) = MvPolynomial.C c * P) :
    ∃ D : FreeAffineCircuit (Fin m),
      ∃ output : FreeAffineForm (Fin m),
        output ∈ D.outputs ∧
        output.eval D.values = P ∧
        D.multiplicationCount ≤ circuit.size := by sorry
