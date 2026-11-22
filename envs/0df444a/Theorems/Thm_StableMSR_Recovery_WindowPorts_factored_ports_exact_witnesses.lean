-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_factored_ports_exact_witnesses
-- name    : StableMSR.Recovery.WindowPorts.factored_ports_exact_witnesses
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:18:37.209266+00:00
-- url     : https://prove2.me/theorems/b104fbad-f9af-4cc4-86cd-1de807ba09e2
-- title:
--   Independent separator choices compile to exactly the same endpoint words at every count
-- statement:
--   Every compiled derivation decodes to two independently permitted separator matches, and every feasible pair compiles to a derivation with the identical padded endpoint word. The argument includes zero counts, empty children, multiple matches and unused labels.
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

theorem StableMSR.Recovery.WindowPorts.factored_ports_exact_witnesses (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) (p c : ℕ) (pc : p< B.size) (ck : c≤ k) (u : Word) :
    Derives k (lower B n k) (finish n p c) u ↔ Reach k B p c u := by sorry
