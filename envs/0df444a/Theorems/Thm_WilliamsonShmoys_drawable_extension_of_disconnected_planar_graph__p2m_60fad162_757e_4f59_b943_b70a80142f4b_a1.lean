-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a1
-- name    : WilliamsonShmoys.drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:42.070324+00:00
-- url     : https://prove2.me/theorems/6d18afc2-3be2-480d-b12d-423544cfb612
-- title:
--   A disconnected drawable graph has a proper drawable extension
-- statement:
--   For a finite ordered vertex type, every disconnected graph with a crossing-free drawing has a proper drawable supergraph on the same vertices. The intended route is to use the finite embedded graph structure to find two components that can be connected by an arc with interior disjoint from the existing drawing, and then add the edge represented by that arc. Disconnectedness supplies distinct components; the child asserts existence of some edge extension, not an extension for a prescribed pair of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ N ≠ M := by sorry
