-- Prove2me | Theorems.Thm_PermanentRollout_pderiv_input_linearCombination
-- name    : PermanentRollout.pderiv_input_linearCombination
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/6e7daa8e-424e-4af3-a09f-f1d9199c556d
-- title:
--   PermanentRollout.pderiv_input_linearCombination
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

theorem PermanentRollout.pderiv_input_linearCombination {ι : Type*} (input : ι)
    (coefficients : ι →₀ ℂ) :
    MvPolynomial.pderiv input
        (Finsupp.linearCombination ℂ MvPolynomial.X coefficients) =
      MvPolynomial.C (coefficients input) := by sorry
