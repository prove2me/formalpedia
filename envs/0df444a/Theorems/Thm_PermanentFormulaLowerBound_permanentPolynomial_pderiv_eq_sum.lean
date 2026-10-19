-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_pderiv_eq_sum
-- name    : PermanentFormulaLowerBound.permanentPolynomial_pderiv_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/bed50be0-0216-4634-8519-7deb6d01fac5
-- title:
--   PermanentFormulaLowerBound.permanentPolynomial_pderiv_eq_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.permanentPolynomial_pderiv_eq_sum
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) =
      ∑ σ : Equiv.Perm (Fin n),
        if σ a = b then
          ∏ i : {i : Fin n // i ≠ a},
            (MvPolynomial.X (i.1, σ i.1) :
              MvPolynomial (Fin n × Fin n) ℂ)
        else 0 := by sorry
