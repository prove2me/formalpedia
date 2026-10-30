-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- name    : WilliamsonShmoys.disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:32:43.602848+00:00
-- url     : https://prove2.me/theorems/093d3833-026f-4cc9-9066-8ef7487e85b6
-- title:
--   A disconnected planar graph has fewer than 3|V|−6 edges
-- statement:
--   A disconnected finite drawable simple graph on at least three vertices has at most 3|V|−7 edges. Componentwise planar edge bounds, with separate treatment for components of size one or two, give this estimate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    G.edgeSet.ncard + 7 ≤ 3 * Fintype.card V := by sorry
