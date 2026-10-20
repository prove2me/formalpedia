-- Prove2me | Theorems.Thm_PermanentRollout_circuitComplexity_attained
-- name    : PermanentRollout.circuitComplexity_attained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/5f996611-2754-4573-af97-3a6ff29a4d69
-- title:
--   PermanentRollout.circuitComplexity_attained
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

theorem PermanentRollout.circuitComplexity_attained {ι : Type}
    (polynomial : MvPolynomial ι ℂ) :
    ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial ∧
        circuit.size = circuitComplexity polynomial := by sorry
