-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension
-- name    : WilliamsonShmoys.drawable_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:32:28.891291+00:00
-- url     : https://prove2.me/theorems/037368dd-04cc-4345-b537-96bdbb1ae146
-- title:
--   Extension of a drawable graph to a triangulation
-- statement:
--   Any drawable simple graph on a finite linearly ordered vertex type with at least three vertices can be extended, without adding vertices, to a drawable graph with exactly 3|V|−6 edges; the extension contains the original graph and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      X ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      X.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
