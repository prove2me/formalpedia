-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_add
-- name    : ShiQMACenteredGap.biasIter_add
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T00:02:52.318932+00:00
-- url     : https://prove2.me/theorems/4a5ec864-8b87-4330-99ab-707a31bfeca1
-- title:
--   Centered majority iterations compose over added round counts
-- statement:
--   Running r+s majority rounds equals running r rounds and then s more rounds.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L17-L21

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasIter_add (d : ℝ) (r s : Nat) :
    biasIter d (r + s) = biasIter (biasIter d r) s := by sorry
