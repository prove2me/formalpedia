-- Prove2me | Theorems.Thm_ShiQMACenteredGap_normalizationRounds_suffice
-- name    : ShiQMACenteredGap.normalizationRounds_suffice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T00:10:35.037418+00:00
-- url     : https://prove2.me/theorems/efa84e25-a28d-4a66-9fd3-265722f1f163
-- title:
--   Logarithmic rounds normalize an inverse-polynomial QMA gap
-- statement:
--   Three rounds per logarithmic precision step raise the centered bias to at least one sixth under the inverse-polynomial gap premise.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L39-L48

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_biasIter_dyadic
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.normalizationRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (normalizationRounds q n) := by sorry
