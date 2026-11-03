-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- name    : WilliamsonShmoys.component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T17:33:46.882533+00:00
-- url     : https://prove2.me/theorems/e2ed5c76-88ec-4a1d-b10e-951419bd4b2c
-- title:
--   Edge count additivity over a disjoint cover
-- statement:
--   For a finite simple graph, if a finite family of vertex blocks is pairwise disjoint and covers every vertex, then the original edge count equals the sum of the edge counts in the induced subgraphs on those blocks. The cover and disjointness conditions also make the claim valid for an empty vertex type and its empty block family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (C : Finset (Finset V)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) →
     (∀ v : V, ∃ B ∈ C, v ∈ B) →
     N.edgeFinset.card =
       ∑ B ∈ C,
         (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
          (N.induce (↑B : Set V)).edgeFinset.card)) := by sorry
