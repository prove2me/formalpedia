-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_eval_congr_of_referencesBounded
-- name    : PermanentRollout.ReverseAdjoint.eval_congr_of_referencesBounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/d47bc362-ac5e-4877-92af-1f1d9dc7a7e9
-- title:
--   PermanentRollout.ReverseAdjoint.eval_congr_of_referencesBounded
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

theorem PermanentRollout.ReverseAdjoint.eval_congr_of_referencesBounded {ι : Type*}
    (instruction : FreeAffineInstruction ι) (position : ℕ)
    (before after : Array (MvPolynomial ι ℂ))
    (hvalid : instruction.referencesBounded position)
    (hvalues : ∀ index < position,
      before.getD index 0 = after.getD index 0) :
    instruction.eval before = instruction.eval after := by sorry
