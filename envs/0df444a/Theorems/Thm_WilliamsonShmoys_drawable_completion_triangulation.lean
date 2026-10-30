-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_completion_triangulation
-- name    : WilliamsonShmoys.drawable_completion_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:23:09.415101+00:00
-- url     : https://prove2.me/theorems/26f5c1b5-8e07-44eb-aceb-0753511a9c41
-- title:
--   Triangulation completion of a drawable graph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V| - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_completion_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn P /\
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
