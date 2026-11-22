-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_uncompressed_bag_derivations
-- name    : StableMSR.Recovery.WindowJoins.uncompressed_bag_derivations
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:41:24.637905+00:00
-- url     : https://prove2.me/theorems/647b5e5c-2d09-474f-a558-8416b9676ad0
-- title:
--   Unoptimized bag productions exactly realize the minima of the finite tree program
-- statement:
--   Before minimizing, the local productions enumerate all compatible bag labels and counts. Every optimized entry has an actual production derivation, and every derivation is dominated by an optimized entry with the same bag labeling and count.
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

theorem StableMSR.Recovery.WindowJoins.uncompressed_bag_derivations {V X : Type} [DecidableEq V] (cap : ℕ) (p : Plan V X) :
    (∀u∈TreeDP.solve cap p,Raw cap p u.1 u.2.1 u.2.2) ∧
    ∀a j w,Raw cap p a j w → ∃t≤ w,(a,(j,t))∈TreeDP.solve cap p := by sorry
