-- Prove2me | Theorems.Thm_ShiQMACenteredGap_encodeCoin_probability
-- name    : ShiQMACenteredGap.encodeCoin_probability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T12:22:46.988084+00:00
-- url     : https://prove2.me/theorems/4d009613-f62a-46f2-8100-f2f35fa6b9de
-- title:
--   Coin code realizes the intended dyadic probability
-- statement:
--   For every j at most 2^k, the executable coin code has probability j/2^k, including the endpoint j=2^k represented by a constant-one code.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c789401/proofs/AMPUNI-computable-centering.lean#L125-L144

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator

set_option autoImplicit false

theorem ShiQMACenteredGap.encodeCoin_probability (k j : Nat) (hj : j ≤ 2 ^ k) :
    (encodeCoin k j).probability = (j : ℝ) / (2 : ℝ) ^ k := by
  sorry
