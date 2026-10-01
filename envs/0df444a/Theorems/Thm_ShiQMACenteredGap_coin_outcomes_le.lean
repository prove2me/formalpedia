-- Prove2me | Theorems.Thm_ShiQMACenteredGap_coin_outcomes_le
-- name    : ShiQMACenteredGap.coin_outcomes_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T09:54:46.601259+00:00
-- url     : https://prove2.me/theorems/06d91314-78dd-496a-b8ef-f755a7203f8b
-- title:
--   Linear bound on dyadic coin outcomes
-- statement:
--   For every positive gap budget q, the coin schedule coinBits(q) has at most 8q possible fair-bit outcomes.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-dyadic-centering.lean#L47-L53

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.coin_outcomes_le (q : Nat) (hq : 0 < q) :
    2 ^ coinBits q ≤ 8 * q := by
  sorry
