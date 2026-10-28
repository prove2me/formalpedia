-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_edge_count_v2
-- name    : WilliamsonShmoys.drawable_completion_maximal_edge_count_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:11:51.036089+00:00
-- url     : https://prove2.me/theorems/ed2ade0e-998a-4ae5-abd6-78a35c2b0eef
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable proper supergraph on those vertices has exactly `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_completion_maximal_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn P ->
      (forall {u v}, P.Adj u v -> N.Adj u v))
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
