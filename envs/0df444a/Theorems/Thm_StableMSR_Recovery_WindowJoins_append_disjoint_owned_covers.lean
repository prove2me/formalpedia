-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_append_disjoint_owned_covers
-- name    : StableMSR.Recovery.WindowJoins.append_disjoint_owned_covers
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:41:13.689808+00:00
-- url     : https://prove2.me/theorems/2b6348db-e880-40c9-bcfc-8aab32e4a11d
-- title:
--   Appending local covers on disjoint supports preserves ownership and exact cost
-- statement:
--   A binary join of disjoint owned subregions is a feasible witness on their union. Its center count and cost both add exactly, and distinct centers follow from disjoint supports.
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

theorem StableMSR.Recovery.WindowJoins.append_disjoint_owned_covers (x : World) (W U : Cluster x.n) (a b : ℕ) (h : a+b≤ x.k) (dis : Disjoint W U)
    (L R : Word) (hl : Owned x W a L) (hr : Owned x U b R) :
    Owned x (W∪U) (a+b) (appendWords x.k a (a+b) L R) ∧
    weight x (a+b) (appendWords x.k a (a+b) L R)=weight x a L+weight x b R := by sorry
