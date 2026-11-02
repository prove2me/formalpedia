-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- name    : WilliamsonShmoys.connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:47.017845+00:00
-- url     : https://prove2.me/theorems/41b40c54-8bb1-4d46-86ef-4c4be4340889
-- title:
--   Connected finite graphs have enough edges
-- statement:
--   A finite graph in which every pair of vertices is joined by a walk has at least one fewer edge than vertices. This supplies the lower numerical bound used to make the constructed face count positive and establish Euler’s equation. A proof route is to take a spanning tree of the connected finite graph and use that a finite tree on `n` vertices has `n - 1` edges. The inequality also holds for the one-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

theorem WilliamsonShmoys.connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : forall u v : V, Nonempty (J.Walk u v)) :
    Fintype.card V <= J.edgeFinset.card + 1 := by sorry
