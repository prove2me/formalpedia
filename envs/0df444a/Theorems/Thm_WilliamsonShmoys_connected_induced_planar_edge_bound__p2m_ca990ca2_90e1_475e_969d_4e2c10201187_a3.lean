-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_bound__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
-- name    : WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:19.303594+00:00
-- url     : https://prove2.me/theorems/11c03224-9a78-4f45-af04-8c20d1b2e25b
-- title:
--   Edge bound for connected induced subgraphs of a drawn graph
-- statement:
--   Every connected induced subgraph on at least three vertices of a graph with a crossing-free drawing has at most 3n−6 edges. This isolates the planar part: restrict the drawing to the selected vertices and apply the connected planar edge count. The size hypothesis excludes the small cases where that count does not hold. The remaining core obligation is formalizing the Euler and face-counting proof for this drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (s : Finset V) (hs : 3 ≤ s.card)
    (hconn : (L.induce (s : Set V)).Connected) :
    (L.induce (s : Set V)).edgeSet.ncard + 6 ≤
      3 * Fintype.card {v // v ∈ (s : Set V)} := by sorry
