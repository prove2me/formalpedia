-- Prove2me | Theorems.Thm_PermanentRollout_pderiv_linearCombination
-- name    : PermanentRollout.pderiv_linearCombination
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/29d250d7-280d-4d39-a8f2-44cd49c24b18
-- title:
--   PermanentRollout.pderiv_linearCombination
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

theorem PermanentRollout.pderiv_linearCombination {ι κ : Type*} (input : ι)
    (family : κ → MvPolynomial ι ℂ) (coefficients : κ →₀ ℂ) :
    MvPolynomial.pderiv input
        (Finsupp.linearCombination ℂ family coefficients) =
      Finsupp.linearCombination ℂ
        (fun index => MvPolynomial.pderiv input (family index))
        coefficients := by sorry
