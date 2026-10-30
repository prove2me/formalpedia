-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- name    : WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:26.420409+00:00
-- url     : https://prove2.me/theorems/385849ac-670b-4bd5-bbc3-be53fd54ea16
-- title:
--   Connected component supports form a structural partition
-- statement:
--   Every vertex lies in exactly one of a finite family of parts; each part induces a connected subgraph, and both endpoints of every edge lie in one part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) := by sorry
