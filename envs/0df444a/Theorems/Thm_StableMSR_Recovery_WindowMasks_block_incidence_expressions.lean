-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowMasks_block_incidence_expressions
-- name    : StableMSR.Recovery.WindowMasks.block_incidence_expressions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:27:31.400498+00:00
-- url     : https://prove2.me/theorems/50f3451c-0be4-41db-93d8-70ea51375057
-- title:
--   Bounded real-distance RAM expressions compute all block charges from incidence bits
-- statement:
--   Finite scans of the point axis find enclosing pairs, compare their radii, and select the least minimizing center and first farthest witness. The resulting arity and endpoints can be tabulated simultaneously for every literal, without writing intermediate assignments.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowBlockMasks
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks

theorem StableMSR.Recovery.WindowMasks.block_incidence_expressions : ∀s : Bool,Form (fun x ρ=>iv (normalized x (ρ 0) (ρ 1) s)) := by sorry
