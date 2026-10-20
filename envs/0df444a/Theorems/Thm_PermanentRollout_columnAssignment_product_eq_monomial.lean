-- Prove2me | Theorems.Thm_PermanentRollout_columnAssignment_product_eq_monomial
-- name    : PermanentRollout.columnAssignment_product_eq_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/8c0c41d9-6ab4-4f5c-9c82-2bbeb43442fb
-- title:
--   PermanentRollout.columnAssignment_product_eq_monomial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.columnAssignment_product_eq_monomial {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (assignment : Fin k → Fin r) :
    (∏ column : Fin k,
      MvPolynomial.C (U (assignment column) column) *
        MvPolynomial.X (assignment column)) =
      MvPolynomial.monomial (columnAssignmentExponent assignment)
        (∏ column : Fin k, U (assignment column) column) := by sorry
