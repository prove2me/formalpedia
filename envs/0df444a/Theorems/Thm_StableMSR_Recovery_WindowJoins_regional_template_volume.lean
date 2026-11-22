-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_regional_template_volume
-- name    : StableMSR.Recovery.WindowJoins.regional_template_volume
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:41:13.582252+00:00
-- url     : https://prove2.me/theorems/1617ad2c-d0ff-4355-897a-d8c7b62f283f
-- title:
--   All unoptimized regional bag and child-count triples fit the required stability exponent
-- statement:
--   For any individual region satisfying the width bound, even the unfiltered rectangular list of parent and two child labels and both child counts has at most n to the 70 times parameter-envelope slots. This bound applies before pruning unreachable, incompatible or nonoptimal labels.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowJoinTemplates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery.TreeDP StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds

theorem StableMSR.Recovery.WindowJoins.regional_template_volume (x : World) (W : Cluster x.n) (R e : ℝ) (ep : 0< e) (el : e<1) (hk : 1≤ x.k) (hn : x.k< x.n)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) (widthBound e)) :
    ∃p : Plan ↥(greedyNet x.dist R W) (Partition x.n),realizesWindows x W R (budget e) (widthBound e) p ∧
      templateSlots x.k p≤ x.n^(70*parameterEnvelope e) := by sorry
