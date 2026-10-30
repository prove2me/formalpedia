-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:09:10.751087+00:00
-- url     : https://prove2.me/theorems/1fede0fd-ca75-4d2a-8cf1-d73a70c51443
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   A connected simple graph on at least three vertices with the supplied noncrossing arc drawing has at most 3|V| − 6 edges. This isolates the Euler and face-boundary counting step; the tree case follows directly from its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hConn : M.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
