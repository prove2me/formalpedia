-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_face_data
-- name    : WilliamsonShmoys.connected_induced_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:33:31.206372+00:00
-- url     : https://prove2.me/theorems/45570c4b-676f-4e28-b259-6b03c905db7f
-- title:
--   Derive face-count data for a large connected induced subgraph
-- statement:
--   For a nonempty connected induced subgraph with at least three vertices, the edge lower bound for connected finite graphs makes f = e + 2 − n natural; the supplied local edge upper bound then proves the required inequality by arithmetic. This removes the per-block face-count reasoning from the parent theorem. A proof route is to apply the connected-graph edge lower bound and normalize the natural-number inequalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_induced_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hlarge : 3 ≤ C.card)
    (hbound : (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card) :
    ∃ f : ℕ,
      C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard := by sorry
