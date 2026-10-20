-- Prove2me | Theorems.Thm_PermanentRollout_FreeAffineInstruction_eval_substituteInputs
-- name    : PermanentRollout.FreeAffineInstruction.eval_substituteInputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/0901b7e4-d3c5-414b-9fe7-b3a689c0834c
-- title:
--   PermanentRollout.FreeAffineInstruction.eval_substituteInputs
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
open PermanentRollout.FreeAffineInstruction

theorem PermanentRollout.FreeAffineInstruction.eval_substituteInputs {ι κ : Type*}
    (substitution : ι → FreeAffineInput κ)
    (instruction : FreeAffineInstruction ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (instruction.substituteInputs substitution).eval
      (values.map (MvPolynomial.aeval
        (fun index => (substitution index).polynomial))) =
      MvPolynomial.aeval
        (fun index => (substitution index).polynomial)
        (instruction.eval values) := by sorry
