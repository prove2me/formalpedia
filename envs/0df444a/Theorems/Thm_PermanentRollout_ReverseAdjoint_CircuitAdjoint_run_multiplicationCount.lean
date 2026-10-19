-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_run_multiplicationCount
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_multiplicationCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/f6faf963-a41a-4263-a910-5dbff3eb6d96
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_multiplicationCount
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
open PermanentRollout.ReverseAdjoint.CircuitAdjoint

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_multiplicationCount {ι : Type*}
    (circuit : FreeAffineCircuit ι) (output : FreeAffineForm ι) :
    (run circuit output).circuit.multiplicationCount =
      3 * circuit.multiplicationCount := by sorry
