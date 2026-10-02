-- Prove2me | Theorems.Thm_ShiQMACenteredGap_generalGapRounds_suffice
-- name    : ShiQMACenteredGap.generalGapRounds_suffice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T00:23:30.110899+00:00
-- url     : https://prove2.me/theorems/c416209c-b990-45fb-8d6b-bf57e3eae8ab
-- title:
--   General-gap schedule reaches the target QMA error
-- statement:
--   After bias normalization and the constructive error-reduction rounds, the centered acceptance bias reaches one half minus the target exponential error.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L51-L60

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_normalizationRounds_suffice
import Theorems.Thm_ShiQMACenteredGap_biasIter_mono
import Theorems.Thm_ShiQMACenteredGap_biasIter_add
import Theorems.Thm_ShiQMACenteredGap_biasIter_standard
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds
import Theorems.Thm_ShiQMAConstructiveSchedule_error_rounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.generalGapRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤ biasIter d (generalGapRounds q p n) := by sorry
