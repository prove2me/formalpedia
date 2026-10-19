-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_step_potential
-- name    : PermanentRollout.ReverseAdjoint.step_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/eeff5c78-bf28-4886-9d29-55b752ceb140
-- title:
--   PermanentRollout.ReverseAdjoint.step_potential
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

theorem PermanentRollout.ReverseAdjoint.step_potential {ι : Type*}
    (values : Array (MvPolynomial ι ℂ))
    (state : ReverseAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ) (input : ι)
    (hgate : values.getD instruction.2 0 =
      instruction.1.eval values) :
    (step values state instruction).potential values input =
      state.potential values input := by sorry
