-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_instructionCost_sum
-- name    : PermanentRollout.ReverseAdjoint.instructionCost_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/f5b495ff-07b2-4430-b670-7e8b76152fa2
-- title:
--   PermanentRollout.ReverseAdjoint.instructionCost_sum
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

theorem PermanentRollout.ReverseAdjoint.instructionCost_sum {ι : Type*}
    (program : List (FreeAffineInstruction ι)) :
    (program.map instructionCost).sum =
      2 * (program.filter FreeAffineInstruction.isMultiplication).length := by sorry
