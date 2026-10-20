-- Prove2me | Theorems.Thm_PermanentRollout_subtree_mul_add_pow_eq_of_annihilates
-- name    : PermanentRollout.subtree_mul_add_pow_eq_of_annihilates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/7cf09dd1-540e-437b-a9fd-621cc3202cdb
-- title:
--   PermanentRollout.subtree_mul_add_pow_eq_of_annihilates
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtree_mul_add_pow_eq_of_annihilates
    {R : Type*} [CommSemiring R] (p x z : R)
    (hp : p * z = 0) (d : ℕ) :
    p * (x + z) ^ d = p * x ^ d := by sorry
