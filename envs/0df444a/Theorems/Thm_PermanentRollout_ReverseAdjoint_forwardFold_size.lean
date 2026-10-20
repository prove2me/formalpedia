-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_size
-- name    : PermanentRollout.ReverseAdjoint.forwardFold_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/79ee7a71-ce0f-4a45-bfdc-d94f3664e656
-- title:
--   PermanentRollout.ReverseAdjoint.forwardFold_size
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

theorem PermanentRollout.ReverseAdjoint.forwardFold_size {ι : Type*}
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ)) :
    (program.foldl forwardStep values).size =
      values.size + program.length := by sorry
