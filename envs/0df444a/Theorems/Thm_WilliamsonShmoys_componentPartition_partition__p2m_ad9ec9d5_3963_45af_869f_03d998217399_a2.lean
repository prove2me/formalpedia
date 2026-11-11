-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentPartition_partition__p2m_ad9ec9d5_3963_45af_869f_03d998217399_a2
-- name    : WilliamsonShmoys.componentPartition_partition__p2m_ad9ec9d5_3963_45af_869f_03d998217399_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:48.869566+00:00
-- url     : https://prove2.me/theorems/053c70ef-f744-4a5d-ac3b-f6cac1b9033a
-- title:
--   Finite partition into connected induced blocks
-- statement:
--   Every finite graph has a partition of its vertices into nonempty blocks whose induced graphs are connected. The blocks cover every vertex, are pairwise disjoint, and their cardinalities sum to the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.componentPartition_partition__p2m_ad9ec9d5_3963_45af_869f_03d998217399_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) := by sorry
