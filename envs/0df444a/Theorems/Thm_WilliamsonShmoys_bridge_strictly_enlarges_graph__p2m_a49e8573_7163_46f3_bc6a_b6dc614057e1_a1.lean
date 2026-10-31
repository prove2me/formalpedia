-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_strictly_enlarges_graph__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- name    : WilliamsonShmoys.bridge_strictly_enlarges_graph__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:28.124998+00:00
-- url     : https://prove2.me/theorems/ca1a43f2-1df2-459f-8941-a20676018a5d
-- title:
--   Adding a missing bridge strictly enlarges a graph
-- statement:
--   Adding a bridge relation between distinct nonadjacent vertices produces a graph that strictly contains the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.bridge_strictly_enlarges_graph__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (u v : V)
    (huv : u ≠ v)
    (hnotadj : ¬ G.Adj u v) :
    G < G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v) := by sorry
