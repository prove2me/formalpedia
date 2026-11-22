-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_native_separator_ports
-- name    : StableMSR.Recovery.WindowPorts.native_separator_ports
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T23:18:24.055413+00:00
-- url     : https://prove2.me/theorems/2301bbed-0665-446f-a523-ff50ed19d6c6
-- title:
--   Construct literal bag choices and independent separator ports for regional windows
-- statement:
--   Produce the regional bag label records, their local endpoint literals, and the individual permissible parent-to-child matches on each separator. The local counts come from literals. The same regional root serves every exact count. No internal state counts, count splits, paired child alternatives, or winner are part of the input to the lowering.
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

theorem StableMSR.Recovery.WindowPorts.native_separator_ports : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,portSpec e c D b cmd := by sorry
