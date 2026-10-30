-- Prove2me | Theorems.Thm_SimpleGraph_preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
-- name    : SimpleGraph.preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:57.883382+00:00
-- url     : https://prove2.me/theorems/7e139eb9-902e-43ae-a2cc-5a720eb5726b
-- title:
--   Propagation of an insertion invariant
-- statement:
--   If P holds for the empty graph and each permitted insertion preserves P, then P holds for G. Prove by inserting the finitely many edges of G one at a time; each prefix remains a subgraph of G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem SimpleGraph.preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (f : SimpleGraph V → ℕ)
    (hzero : P ⊥ ∧ f ⊥ = 1)
    (hadd : ∀ (H : SimpleGraph V), H ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ H.Adj u v →
      P H →
        P (H ⊔ SimpleGraph.edge u v) ∧
        (H.Reachable u v → f (H ⊔ SimpleGraph.edge u v) = f H + 1) ∧
        (¬ H.Reachable u v → f (H ⊔ SimpleGraph.edge u v) = f H)) :
    P G := by sorry
