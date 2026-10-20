-- Prove2me | Theorems.Thm_PermanentRollout_coeff_squareFreeMonomial_mul
-- name    : PermanentRollout.coeff_squareFreeMonomial_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/1ddee8be-74d2-4caa-b3c1-a67f13c18938
-- title:
--   PermanentRollout.coeff_squareFreeMonomial_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.coeff_squareFreeMonomial_mul {ι : Type*} [DecidableEq ι]
    (target removed : Finset ι) (p : MvPolynomial ι ℂ) :
    MvPolynomial.coeff (squareFreeExponent target)
      (squareFreeMonomial removed * p) =
        if removed ⊆ target then
          MvPolynomial.coeff (squareFreeExponent (target \ removed)) p
        else 0 := by sorry
