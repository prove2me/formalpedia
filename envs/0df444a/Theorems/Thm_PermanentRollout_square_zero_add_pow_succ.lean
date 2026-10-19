-- Prove2me | Theorems.Thm_PermanentRollout_square_zero_add_pow_succ
-- name    : PermanentRollout.square_zero_add_pow_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/7d407aa8-0374-4555-a9a9-fbc96ff2942e
-- title:
--   PermanentRollout.square_zero_add_pow_succ
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.square_zero_add_pow_succ {R : Type*} [CommSemiring R]
    {x y : R} {n : ℕ} (hx : x ^ 2 = 0) (hy : y ^ (n + 1) = 0) :
    (x + y) ^ (n + 1) = (n + 1 : ℕ) * x * y ^ n := by sorry
