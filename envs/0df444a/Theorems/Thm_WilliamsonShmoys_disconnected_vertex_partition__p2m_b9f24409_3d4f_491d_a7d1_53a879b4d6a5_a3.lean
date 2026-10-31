-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a3
-- name    : WilliamsonShmoys.disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:20.766586+00:00
-- url     : https://prove2.me/theorems/cb1ec9fc-b85b-4e24-bcb5-b44b812b55dc
-- title:
--   Separate a nonempty disconnected graph into nonempty parts
-- statement:
--   A finite disconnected graph with at least three vertices can be partitioned into two nonempty vertex sets with no edges crossing between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDisc : ¬ M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ M.Adj u v) := by sorry
