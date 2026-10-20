-- Prove2me | Theorems.Thm_PermanentRollout_squareFreeMonomial_quotient_eq_variable_product
-- name    : PermanentRollout.squareFreeMonomial_quotient_eq_variable_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/62a32bd1-3307-4a07-959d-c145181c4221
-- title:
--   PermanentRollout.squareFreeMonomial_quotient_eq_variable_product
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareFreeMonomial_quotient_eq_variable_product
    (r : ℕ) (rows : Finset (Fin r)) :
    Ideal.Quotient.mk (squareZeroIdeal r) (squareFreeMonomial rows) =
      ∏ i ∈ rows, squareZeroVariable r i := by sorry
