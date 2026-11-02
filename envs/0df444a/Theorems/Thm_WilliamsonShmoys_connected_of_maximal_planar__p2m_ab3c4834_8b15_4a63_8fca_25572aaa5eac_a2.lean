-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- name    : WilliamsonShmoys.connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:50.344488+00:00
-- url     : https://prove2.me/theorems/60fad162-757e-4f59-b943-b70a80142f4b
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type is connected. This separates the connectivity consequence of maximality from face counting. A proof route is to start with a disconnected drawing, connect two components by a new edge routed through the complement of the finite drawing, and contradict maximality; formalizing this requires first replacing the given finite family of continuous arcs with a suitable plane-embedding representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.Connected := by sorry
