-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_initial_potential
-- name    : PermanentRollout.ReverseAdjoint.initial_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/3fd16981-c550-4b19-893d-77b4f23f11a3
-- title:
--   PermanentRollout.ReverseAdjoint.initial_potential
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

theorem PermanentRollout.ReverseAdjoint.initial_potential {ι : Type*}
    (output : FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) (input : ι) :
    (initial output).potential values input =
      MvPolynomial.pderiv input (output.eval values) := by sorry
