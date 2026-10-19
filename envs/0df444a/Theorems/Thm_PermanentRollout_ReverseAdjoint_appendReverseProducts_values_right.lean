-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values_right
-- name    : PermanentRollout.ReverseAdjoint.appendReverseProducts_values_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/882beb14-c822-4e10-b843-cb0a163f9615
-- title:
--   PermanentRollout.ReverseAdjoint.appendReverseProducts_values_right
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

theorem PermanentRollout.ReverseAdjoint.appendReverseProducts_values_right {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).values.getD
        (circuit.program.length + 1) 0 =
          adjoint.eval circuit.values * circuit.values.getD right 0 := by sorry
