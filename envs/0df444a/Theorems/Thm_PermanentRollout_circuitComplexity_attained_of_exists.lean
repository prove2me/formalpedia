-- Prove2me | Theorems.Thm_PermanentRollout_circuitComplexity_attained_of_exists
-- name    : PermanentRollout.circuitComplexity_attained_of_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/eec7f31d-c777-4395-a007-3bd61f022537
-- title:
--   PermanentRollout.circuitComplexity_attained_of_exists
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

theorem PermanentRollout.circuitComplexity_attained_of_exists {ι : Type}
    (polynomial : MvPolynomial ι ℂ)
    (hrepresentable : ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial) :
    ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial ∧
        circuit.size = circuitComplexity polynomial := by sorry
