-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_simple_graph_edge_bound
-- name    : WilliamsonShmoys.drawable_simple_graph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:03:50.903253+00:00
-- url     : https://prove2.me/theorems/5eeda581-5b51-434a-81ea-ebfbdf570c5a
-- title:
--   Edge bound for a drawable simple graph
-- statement:
--   A drawable simple graph on at least three vertices has at most 3|V|−6 edges. This is the Euler-formula upper bound, with disconnected graphs handled by their components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_simple_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
