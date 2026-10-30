-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- name    : WilliamsonShmoys.bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:56.480879+00:00
-- url     : https://prove2.me/theorems/0f3136e5-b2ea-4ac1-bb80-76e0f6df8212
-- title:
--   Add an unreachable pair as a graph edge
-- statement:
--   Add exactly the unordered pair `{u,v}` to the graph. The resulting simple graph extends `G`, contains the new edge, and has no other new edges; non-reachability ensures this edge was not already present.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u < v)
    (hreach : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (∀ x y, H.Adj x y ↔
        G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
      H.Adj u v ∧ ¬ G.Adj u v := by sorry
