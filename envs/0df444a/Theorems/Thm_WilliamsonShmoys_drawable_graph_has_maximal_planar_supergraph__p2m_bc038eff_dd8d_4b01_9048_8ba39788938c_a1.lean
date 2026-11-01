-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:10.028212+00:00
-- url     : https://prove2.me/theorems/9b388be1-04ba-4932-ab10-78f95ba0c0d7
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on at least three finite ordered vertices has a drawable supergraph on the same vertices that contains every drawable supergraph of the original graph. This captures maximality among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V,
        (forall {u v : V}, K.Adj u v -> M.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn M ->
        (forall {u v : V}, M.Adj u v -> L.Adj u v)) := by sorry
