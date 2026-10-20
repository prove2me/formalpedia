-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_eq_sum
-- name    : PermanentFormulaLowerBound.permanentPolynomial_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/c94d1e79-2516-4af7-a9f1-b8446fd29300
-- title:
--   PermanentFormulaLowerBound.permanentPolynomial_eq_sum
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

theorem PermanentFormulaLowerBound.permanentPolynomial_eq_sum (n : ℕ) :
    permanentPolynomial n =
      ∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin n, MvPolynomial.X (i, σ i) := by sorry
