-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_zipIdx_instructionCost_sum
-- name    : PermanentRollout.ReverseAdjoint.zipIdx_instructionCost_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/33ef0178-8a00-44a8-8fe4-78f2ef74c23f
-- title:
--   PermanentRollout.ReverseAdjoint.zipIdx_instructionCost_sum
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

theorem PermanentRollout.ReverseAdjoint.zipIdx_instructionCost_sum {ι : Type*}
    (program : List (FreeAffineInstruction ι)) (start : ℕ) :
    ((program.zipIdx start).map (fun instruction =>
      instructionCost instruction.1)).sum =
      (program.map instructionCost).sum := by sorry
