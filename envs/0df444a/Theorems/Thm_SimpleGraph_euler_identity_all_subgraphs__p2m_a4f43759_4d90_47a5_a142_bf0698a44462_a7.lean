-- Prove2me | Theorems.Thm_SimpleGraph_euler_identity_all_subgraphs__p2m_a4f43759_4d90_47a5_a142_bf0698a44462_a7
-- name    : SimpleGraph.euler_identity_all_subgraphs__p2m_a4f43759_4d90_47a5_a142_bf0698a44462_a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:15.526055+00:00
-- url     : https://prove2.me/theorems/32fb842e-c5cc-4fb3-a16d-c8f1f928ca75
-- title:
--   Euler invariant for all subgraphs
-- statement:
--   For every subgraph `H ≤ G`, the base value and edge-increment hypotheses imply the Euler identity for `H`. The child removes the finite edge-insertion induction from the parent, which then follows by taking `H = G`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem SimpleGraph.euler_identity_all_subgraphs__p2m_a4f43759_4d90_47a5_a142_bf0698a44462_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (f : SimpleGraph V → ℕ)
    (hzero : P ⊥ ∧ f ⊥ = 1)
    (hadd : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      P K →
        P (K ⊔ SimpleGraph.edge u v) ∧
        (K.Reachable u v → f (K ⊔ SimpleGraph.edge u v) = f K + 1) ∧
        (¬ K.Reachable u v → f (K ⊔ SimpleGraph.edge u v) = f K))
    (H : SimpleGraph V) (hHG : H ≤ G) :
    Fintype.card V + f H =
      H.edgeSet.ncard + Nat.card H.ConnectedComponent + 1 := by sorry
