-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_count_upper_bound
-- name    : WilliamsonShmoys.drawable_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:05:40.211004+00:00
-- url     : https://prove2.me/theorems/cde84d52-afde-4ca1-ab9c-5b2c8d4a1a21
-- title:
--   Drawable simple graphs satisfy the planar edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges. This is the Euler-count half of the argument. A proof route is to handle connected components, apply Euler’s formula to a planar embedding, and use simplicity to bound face boundary lengths, with the three-vertex boundary case treated explicitly. The hypothesis n≥3 is needed for this simple-graph bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
