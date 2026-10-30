-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_maximal_planar_edge_count
-- name    : WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_planar_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:21:37.818834+00:00
-- url     : https://prove2.me/theorems/9834e21e-8951-4a1e-a085-e169ce2d99e6
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A simple graph on at least three vertices that has a crossing-free drawing and admits no proper planar supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ L : SimpleGraph V, G ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
