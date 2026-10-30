-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- name    : WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:57.695312+00:00
-- url     : https://prove2.me/theorems/9357b4e9-1465-44fb-ab01-49fb91da15d0
-- title:
--   Connected planar graph Euler edge bound
-- statement:
--   A finite simple graph on at least three vertices with a connected crossing-free drawing has at most 3|V|−6 edges. This removes the topological and Euler-counting obligation from the parent; the parent applies it to H. Its exact connectedness and size hypotheses are preserved. A proof route is to derive a rotation system from the drawing, apply Euler’s formula and incidence counting, and bound face lengths using simplicity and the three-vertex condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
