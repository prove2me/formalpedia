-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_reverseFold_gateAdjoints_lt
-- name    : PermanentRollout.ReverseAdjoint.reverseFold_gateAdjoints_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/f1717292-df12-4b91-87e2-06e5a8c1fc84
-- title:
--   PermanentRollout.ReverseAdjoint.reverseFold_gateAdjoints_lt
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

theorem PermanentRollout.ReverseAdjoint.reverseFold_gateAdjoints_lt {ι : Type*}
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ)) (start : ℕ)
    (state : ReverseAdjoint ι)
    (hvalid : ∀ instruction ∈ program.zipIdx start,
      instruction.1.referencesBounded instruction.2)
    (hstate : ∀ index, state.gateAdjoints index ≠ 0 →
      index < start + program.length) :
    ∀ index,
      (((program.zipIdx start).reverse).foldl (step values)
        state).gateAdjoints index ≠ 0 → index < start := by sorry
