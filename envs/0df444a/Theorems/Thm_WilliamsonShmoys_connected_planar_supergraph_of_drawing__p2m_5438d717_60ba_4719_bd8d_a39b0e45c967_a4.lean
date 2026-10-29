-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
-- name    : WilliamsonShmoys.connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:03:06.152006+00:00
-- url     : https://prove2.me/theorems/df1c1607-3895-4286-a8a2-9e1999a7ed48
-- title:
--   Connect a nonempty planar drawing without adding vertices
-- statement:
--   For a drawn graph on at least three vertices, add edges on the same vertex set to obtain a connected graph that still has a planar drawing and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
