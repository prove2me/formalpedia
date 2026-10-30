-- Prove2me | Theorems.Thm_WilliamsonShmoys_add_one_edge_subgraph__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
-- name    : WilliamsonShmoys.add_one_edge_subgraph__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:16:04.302996+00:00
-- url     : https://prove2.me/theorems/2d797cff-4194-409d-8fef-b7c46fdc1bc6
-- title:
--   Add one missing edge while staying inside a finite supergraph
-- statement:
--   This reduces the parent to finite edge selection and graph construction. Since `hE` gives `K.edgeSet.ncard + 6 < 3 * Fintype.card V` and `hTcard` identifies T's count with the corresponding natural subtraction, arithmetic yields `K.edgeSet.ncard < T.edgeSet.ncard`. Thus the inclusion is strict and there is an edge of T not in K. Define L by adjoining that edge to K; it contains K, stays within T, and has exactly one additional edge. The strict inequality also excludes the equality boundary; if the vertex count is too small for the subtraction bound, `hE` itself is impossible.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.add_one_edge_subgraph__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K T : SimpleGraph V)
    (hKT : K.edgeSet ⊆ T.edgeSet)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V)
    (hTcard : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ⊆ T.edgeSet ∧
      L.edgeSet.ncard = K.edgeSet.ncard + 1 := by sorry
