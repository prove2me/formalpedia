-- Prove2me | Theorems.Thm_PermanentRollout_squareZeroCoefficient_variable_product_mul
-- name    : PermanentRollout.squareZeroCoefficient_variable_product_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/c1065aa7-0bdc-4b4e-bfc3-c7c23a367b58
-- title:
--   PermanentRollout.squareZeroCoefficient_variable_product_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareZeroCoefficient_variable_product_mul (r : ℕ)
    (target removed : Finset (Fin r)) (p : SquareZeroAlgebra r) :
    squareZeroCoefficient r target
      ((∏ i ∈ removed, squareZeroVariable r i) * p) =
        if removed ⊆ target then
          squareZeroCoefficient r (target \ removed) p
        else 0 := by sorry
