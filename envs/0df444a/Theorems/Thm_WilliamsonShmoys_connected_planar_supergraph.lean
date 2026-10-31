-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph
-- name    : WilliamsonShmoys.connected_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:19:30.735681+00:00
-- url     : https://prove2.me/theorems/abf9a54f-bd26-416c-a90d-ba6fec70cb6a
-- title:
--   Connected planar supergraph extension
-- statement:
--   Extend the given finite planar drawing to a connected planar graph on the same vertices, retaining all original edges and at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
