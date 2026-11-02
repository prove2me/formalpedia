-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- name    : WilliamsonShmoys.componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:06:40.095134+00:00
-- url     : https://prove2.me/theorems/720b2edc-93eb-40a7-9adc-8e9d61e57e08
-- title:
--   Connected-component blocks cover vertices and contain edges
-- statement:
--   Every finite graph admits a partition of its vertices into nonempty blocks whose induced subgraphs are connected, and every edge has both endpoints in one block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by sorry
