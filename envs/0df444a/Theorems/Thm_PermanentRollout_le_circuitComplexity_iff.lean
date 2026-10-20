-- Prove2me | Theorems.Thm_PermanentRollout_le_circuitComplexity_iff
-- name    : PermanentRollout.le_circuitComplexity_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/b6f171be-baa6-4d2e-b7fb-bf5b1efff87c
-- title:
--   PermanentRollout.le_circuitComplexity_iff
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

theorem PermanentRollout.le_circuitComplexity_iff {ι : Type}
    (polynomial : MvPolynomial ι ℂ)
    (bound : ℕ) :
    bound ≤ circuitComplexity polynomial ↔
      ∀ circuit : ArithmeticCircuit ι,
        circuit.polynomial = polynomial → bound ≤ circuit.size := by sorry
