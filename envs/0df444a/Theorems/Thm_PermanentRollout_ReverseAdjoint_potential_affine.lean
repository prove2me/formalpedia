-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_potential_affine
-- name    : PermanentRollout.ReverseAdjoint.potential_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/84d21a8b-3369-4550-8d06-338174785e77
-- title:
--   PermanentRollout.ReverseAdjoint.potential_affine
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

theorem PermanentRollout.ReverseAdjoint.potential_affine {ι : Type*}
    (state : ReverseAdjoint ι)
    (values : Array (MvPolynomial ι ℂ))
    (position : ℕ) (form : FreeAffineForm ι) (input : ι)
    (hgate : values.getD position 0 = form.eval values) :
    (state.affine position form).potential values input =
      state.potential values input := by sorry
