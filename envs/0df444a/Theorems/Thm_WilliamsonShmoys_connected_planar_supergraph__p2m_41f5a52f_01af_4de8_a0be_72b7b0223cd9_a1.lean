-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1
-- name    : WilliamsonShmoys.connected_planar_supergraph__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:46.194238+00:00
-- url     : https://prove2.me/theorems/13169fdd-e716-436e-9a26-b88cf8643106
-- title:
--   Connect components of a planar drawing by adding edges
-- statement:
--   Every finite simply drawn graph can be extended, on the same vertices, to a connected simple graph that still has a crossing-free drawing. Since vertices are distinct and the vertex set is finite, components can be joined successively by arcs routed through the complement of the existing drawing; the construction must preserve the endpoint-only intersection condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
