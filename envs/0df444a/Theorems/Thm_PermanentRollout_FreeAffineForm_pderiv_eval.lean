-- Prove2me | Theorems.Thm_PermanentRollout_FreeAffineForm_pderiv_eval
-- name    : PermanentRollout.FreeAffineForm.pderiv_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/79a7387e-b198-43aa-bfb2-072d254259dd
-- title:
--   PermanentRollout.FreeAffineForm.pderiv_eval
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

theorem PermanentRollout.FreeAffineForm.pderiv_eval {ι : Type*}
    (form : FreeAffineForm ι) (values : Array (MvPolynomial ι ℂ))
    (input : ι) :
    MvPolynomial.pderiv input (form.eval values) =
      MvPolynomial.C (form.inputCoefficients input) +
        Finsupp.linearCombination ℂ
          (fun gate => MvPolynomial.pderiv input
            (values.getD gate 0)) form.gateCoefficients := by sorry
