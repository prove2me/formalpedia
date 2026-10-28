-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_planar_bridge_extension
-- name    : WilliamsonShmoys.connected_supergraph_of_planar_bridge_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:21:03.366081+00:00
-- url     : https://prove2.me/theorems/4f7640b8-c948-48dd-ae1f-43a63672e10d
-- title:
--   Iterate planar bridge extensions to obtain a connected supergraph
-- statement:
--   Given a bridge-extension operation for every disconnected finite planar drawing, iterate it finitely to obtain a walk-connected planar supergraph that retains the original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_supergraph_of_planar_bridge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (bridge_extension : ∀ (K : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ (∀ u v : V, Nonempty (K.Walk u v)) →
      ∃ L : SimpleGraph V,
        K ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (K.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
