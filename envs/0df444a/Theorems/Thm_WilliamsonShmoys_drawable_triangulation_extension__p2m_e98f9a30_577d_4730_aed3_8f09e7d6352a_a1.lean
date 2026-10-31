-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
-- name    : WilliamsonShmoys.drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:41.635749+00:00
-- url     : https://prove2.me/theorems/c8388ff0-77e3-49f1-bb1d-428d2f9c95cd
-- title:
--   Triangulation completion edge lower bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with at least 3(n−2) edges. This child isolates the augmentation and Euler-counting work; the parent applies maximality to the completed graph, obtains equality with the original graph, and transfers the bound. A proof route is to add noncrossing diagonals inside nontriangular faces until the drawing is maximal, then use Euler’s formula and triangular face boundaries to count edges. For the boundary case n=3, the completion is a triangle; the stated lower bound is six in the target’s expression 3*(n−2), which counts each edge twice in the triangulation-style incidence count, so the child’s edge bound is expected to be checked against the exact edge-count convention.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * (Fintype.card V - 2) ≤ H.edgeSet.ncard := by sorry
