-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
-- name    : WilliamsonShmoys.connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:38.41453+00:00
-- url     : https://prove2.me/theorems/feadab3c-5ccb-4a82-9ee7-4f0db9bfa441
-- title:
--   Edge bound for a connected maximal drawable graph
-- statement:
--   For a connected drawable graph on at least three vertices, maximality among drawable supergraphs implies the planar edge bound. The proof route is to extend the drawing to a triangulated plane embedding, count edge-face incidences, and apply Euler’s formula. This child isolates the geometric embedding and planar counting work after connectedness has been established.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) (hUmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) (hconn : U.Connected) : 3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by sorry
