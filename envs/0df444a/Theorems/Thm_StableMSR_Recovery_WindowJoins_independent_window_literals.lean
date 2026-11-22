-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_independent_window_literals
-- name    : StableMSR.Recovery.WindowJoins.independent_window_literals
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:41:25.707802+00:00
-- url     : https://prove2.me/theorems/e8199a8e-a21e-4184-8ecc-ca05198791c1
-- title:
--   Local window contributions admit fixed endpoint words on disjoint owned supports
-- statement:
--   One function assigns endpoint words to individual window labels in advance. An owned block pays its exact discrete radius, and under any compatible family the owned supports are pairwise disjoint and exhaust the region.
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

theorem StableMSR.Recovery.WindowJoins.independent_window_literals (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (dm : IsMetricArray x.dist) (hr : 0≤ R) :
    let N:=greedyNet x.dist R W;let owner:=anchor x.dist W R
    ∃F : Point x.n→Partition x.n→Word,
      (∀a∈N,∀Q∈traceMenu x h (window x.dist W R a),let D:=owned owner a Q
        D.card≤ x.k → Owned x (D.biUnion id) D.card (F a Q) ∧ weight x D.card (F a Q)=cost x.dist D ∧
          ∀j< D.card,∀s,∃p∈D.biUnion id,F a Q j s=(p.val:ℤ)) ∧
      ∀P : Pick x.n,valid x W R h P →
        let S:=fun a=>(owned owner a (P a)).biUnion id
        (N : Set (Point x.n)).PairwiseDisjoint S ∧ N.biUnion S=W := by sorry
