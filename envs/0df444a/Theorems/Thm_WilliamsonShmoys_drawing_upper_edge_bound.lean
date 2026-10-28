-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_upper_edge_bound
-- name    : WilliamsonShmoys.drawing_upper_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:50:00.849987+00:00
-- url     : https://prove2.me/theorems/8303c760-43af-4045-97b9-d010cc2cd13f
-- title:
--   Planar upper edge bound
-- statement:
--   Every graph admitting the specified crossing-free drawing, with at least three vertices, has at most 3n−6 edges. This is the standard planar simple-graph edge bound, derived from Euler’s formula and the fact that face boundaries have length at least three, with the usual care for disconnected graphs and small components. For n=3 the bound is three edges. The lower bound child supplies the opposite inequality under maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawing_upper_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
