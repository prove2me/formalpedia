-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- name    : WilliamsonShmoys.componentwise_edge_bound_aggregate__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:17.617925+00:00
-- url     : https://prove2.me/theorems/be3c76fd-0a91-4933-b3e9-0bd34bf9ab05
-- title:
--   Aggregate edge bounds over connected induced subgraphs
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the Euler edge bound, then the whole graph does too, provided the whole graph has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.componentwise_edge_bound_aggregate__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard ≤ 3 * S.card - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
