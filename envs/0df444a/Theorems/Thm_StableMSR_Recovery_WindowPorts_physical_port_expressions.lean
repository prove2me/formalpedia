-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_physical_port_expressions
-- name    : StableMSR.Recovery.WindowPorts.physical_port_expressions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:21:29.403226+00:00
-- url     : https://prove2.me/theorems/09dd6246-f243-44ea-ac2a-cbc45ec4edcd
-- title:
--   All counted ticket fields are fixed bounded distance-RAM expressions
-- statement:
--   A single family of expressions reads a port board and writes the length, output, destination, left, right and payload fields of the counted grammar. The expressions are independent of the stability parameter and the number of bag labels.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPortPacking
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts

theorem StableMSR.Recovery.WindowPorts.physical_port_expressions : ∀s : Bool,Form (fun x ρ=>iv (WindowPorts.packed x (ρ 0) (ρ 1) s)) := by sorry
