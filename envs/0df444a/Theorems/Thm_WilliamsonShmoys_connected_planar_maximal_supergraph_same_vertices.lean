-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_supergraph_same_vertices
-- name    : WilliamsonShmoys.connected_planar_maximal_supergraph_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:28:31.941657+00:00
-- url     : https://prove2.me/theorems/6db23f2c-8bdd-43de-a53c-f8b2e7fbacc8
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every connected drawable finite graph has a drawable supergraph on the same vertices that remains connected and is maximal among drawable supergraphs. Finiteness gives a direct proof route: maximize edge count among drawable supergraphs containing the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_maximal_supergraph_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
