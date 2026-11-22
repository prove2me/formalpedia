-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_counted_ticket_classification
-- name    : StableMSR.Recovery.WindowPorts.counted_ticket_classification
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:18:33.858949+00:00
-- url     : https://prove2.me/theorems/25ce57f1-460a-4201-b0a6-7ba6d1178dae
-- title:
--   Every active counted ticket has exactly one of four explicit forms
-- statement:
--   Classify every active physical production as the empty witness, a typed literal, a left selector or a right contraction. Bounding and decoding the mixed-radix address rules out spurious productions.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts

theorem StableMSR.Recovery.WindowPorts.counted_ticket_classification (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) (v z : ℕ) :
    WindowJoins.arc (lower B n k) v z ↔ TicketCase B n k v z := by sorry
