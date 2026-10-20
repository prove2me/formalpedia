-- Prove2me | Theorems.Thm_PermanentRollout_real_le_circuitComplexity_iff
-- name    : PermanentRollout.real_le_circuitComplexity_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/2e757f4e-0772-48d5-b931-25dc94f29cc6
-- title:
--   PermanentRollout.real_le_circuitComplexity_iff
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

theorem PermanentRollout.real_le_circuitComplexity_iff {ι : Type}
    (polynomial : MvPolynomial ι ℂ)
    (bound : ℝ) :
    bound ≤ (circuitComplexity polynomial : ℝ) ↔
      ∀ circuit : ArithmeticCircuit ι,
        circuit.polynomial = polynomial → bound ≤ (circuit.size : ℝ) := by sorry
