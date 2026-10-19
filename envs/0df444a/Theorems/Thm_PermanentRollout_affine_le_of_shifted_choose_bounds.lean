-- Prove2me | Theorems.Thm_PermanentRollout_affine_le_of_shifted_choose_bounds
-- name    : PermanentRollout.affine_le_of_shifted_choose_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/fb3b2746-1a82-49a5-b8ae-0949cbf16996
-- title:
--   PermanentRollout.affine_le_of_shifted_choose_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.affine_le_of_shifted_choose_bounds
    (L P n M₀ : ℕ)
    (hbound : ∀ m : ℕ,
      L * (m + n).choose n ≤
        P * (m + M₀ + n).choose n) :
    L ≤ P := by sorry
