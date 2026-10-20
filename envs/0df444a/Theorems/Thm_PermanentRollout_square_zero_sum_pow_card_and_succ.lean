-- Prove2me | Theorems.Thm_PermanentRollout_square_zero_sum_pow_card_and_succ
-- name    : PermanentRollout.square_zero_sum_pow_card_and_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/577266c3-f638-4b3b-b464-de0aca19f073
-- title:
--   PermanentRollout.square_zero_sum_pow_card_and_succ
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.square_zero_sum_pow_card_and_succ {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (z : ι → R)
    (hz : ∀ i ∈ s, z i ^ 2 = 0) :
    ((∑ i ∈ s, z i) ^ s.card = (s.card.factorial : R) * ∏ i ∈ s, z i) ∧
      (∑ i ∈ s, z i) ^ (s.card + 1) = 0 := by sorry
