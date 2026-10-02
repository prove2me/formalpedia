-- Prove2me | Theorems.Thm_ShiQMACenteredGap_existing_rounds_suffice
-- name    : ShiQMACenteredGap.existing_rounds_suffice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T01:41:24.563159+00:00
-- url     : https://prove2.me/theorems/38e654d4-1db6-4822-bc94-4238541d1f6a
-- title:
--   Concrete uniform-generator schedule reaches target QMA error
-- statement:
--   The existing generator round count reaches the centered bias required for the target exponential error under an inverse-polynomial starting gap.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L50-L55

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_suffice
import Theorems.Thm_ShiQMACenteredGap_biasIter_rounds_mono
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_le_existing

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.existing_rounds_suffice {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤
      biasIter d (rounds (gapPolynomial q p) n) := by sorry
