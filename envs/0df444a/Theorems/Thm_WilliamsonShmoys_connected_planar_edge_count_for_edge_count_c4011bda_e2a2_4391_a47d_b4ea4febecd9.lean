-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:28:02.735241+00:00
-- url     : https://prove2.me/theorems/ebe2fe48-3b22-4672-8ecb-0d78f061f679
-- title:
--   Connected simple planar graphs have at most 3n − 6 edges
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. This is the Euler-formula and facial-incidence-counting step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
