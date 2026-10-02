-- Prove2me | Theorems.Thm_ShiQMACenteredGap_generalGapRounds_controller_form
-- name    : ShiQMACenteredGap.generalGapRounds_controller_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T00:33:28.658926+00:00
-- url     : https://prove2.me/theorems/8a6d29b9-a78c-45f3-a8c2-3a7ea275a5d3
-- title:
--   General-gap round count has affine-logarithmic controller form
-- statement:
--   The sum of normalization and error-reduction rounds equals an explicit affine expression in the logarithm of input length plus one.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L62-L67

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.generalGapRounds_controller_form (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n =
      (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4) +
      (3 * q.natDegree + p.natDegree) * (Nat.log 2 (n + 1) + 1) := by sorry
