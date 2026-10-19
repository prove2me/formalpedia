-- Prove2me | Theorems.Thm_PermanentRollout_ArithmeticCircuit_polynomial_eq_getElem
-- name    : PermanentRollout.ArithmeticCircuit.polynomial_eq_getElem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/c2014591-5b6c-4a27-8197-26615e2add01
-- title:
--   PermanentRollout.ArithmeticCircuit.polynomial_eq_getElem
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
open PermanentRollout.ArithmeticCircuit

theorem PermanentRollout.ArithmeticCircuit.polynomial_eq_getElem {ι : Type}
    (circuit : ArithmeticCircuit ι)
    (houtput : circuit.output < circuit.values.size) :
    circuit.polynomial =
      circuit.values[circuit.output]'houtput := by sorry
