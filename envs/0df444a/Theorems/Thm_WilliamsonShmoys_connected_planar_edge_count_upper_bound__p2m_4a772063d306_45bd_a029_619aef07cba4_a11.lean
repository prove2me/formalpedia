-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:02:27.597086+00:00
-- url     : https://prove2.me/theorems/7f650108-6ccf-4d17-bc3a-8aaf85907826
-- title:
--   Connected planar edge count upper bound
-- statement:
--   A finite connected simple graph with a HasPlanarDrawingOn drawing and at least three vertices has at most 3|V| − 6 edges. This isolates the Euler and face-incidence argument; an independent route is an embedding, Euler's formula, two incidences per edge (including bridges), and the minimum face-length count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hConnected : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
