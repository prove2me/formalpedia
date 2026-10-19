-- Prove2me | Theorems.Thm_PermanentRollout_coeff_columnLinearFormProduct_eq_assignment_sum
-- name    : PermanentRollout.coeff_columnLinearFormProduct_eq_assignment_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/750e5f1c-6cc2-4fbc-9247-6a3150fa506b
-- title:
--   PermanentRollout.coeff_columnLinearFormProduct_eq_assignment_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.coeff_columnLinearFormProduct_eq_assignment_sum {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (rows : Finset (Fin r)) :
    MvPolynomial.coeff (squareFreeExponent rows)
      (columnLinearFormProduct U) =
        ∑ assignment : Fin k → Fin r,
          if columnAssignmentExponent assignment = squareFreeExponent rows
          then ∏ column : Fin k, U (assignment column) column
          else 0 := by sorry
