-- Prove2me | Theorems.Thm_PermanentRollout_squareZeroBlockSum_pow_card
-- name    : PermanentRollout.squareZeroBlockSum_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/b795c424-5365-4cc7-94e8-5f929e6eccc0
-- title:
--   PermanentRollout.squareZeroBlockSum_pow_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareZeroBlockSum_pow_card (r : ℕ) (block : Finset (Fin r)) :
    squareZeroBlockSum r block ^ block.card =
      (block.card.factorial : SquareZeroAlgebra r) *
        ∏ i ∈ block, squareZeroVariable r i := by sorry
