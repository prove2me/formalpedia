-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_foldl_potential
-- name    : PermanentRollout.ReverseAdjoint.foldl_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/1ad80ac3-b234-4583-a09f-36621a353dfb
-- title:
--   PermanentRollout.ReverseAdjoint.foldl_potential
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

theorem PermanentRollout.ReverseAdjoint.foldl_potential {ι : Type*}
    (values : Array (MvPolynomial ι ℂ))
    (instructions : List (FreeAffineInstruction ι × ℕ))
    (state : ReverseAdjoint ι) (input : ι)
    (hgate : ∀ instruction ∈ instructions,
      values.getD instruction.2 0 = instruction.1.eval values) :
    (instructions.foldl (step values) state).potential values input =
      state.potential values input := by sorry
