-- Prove2me | Theorems.Thm_WilliamsonShmoys_compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
-- name    : WilliamsonShmoys.compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:24.738574+00:00
-- url     : https://prove2.me/theorems/0609a56d-51e5-4256-a534-917c2073f24d
-- title:
--   Compact locally connected metric spaces have local arc neighborhoods
-- statement:
--   For each point in a compact locally connected metric subspace and each open neighborhood of that point, there is a smaller open neighborhood such that every distinct point in the smaller neighborhood can be joined to the original point by an injective continuous arc lying in the original neighborhood.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2 {X : Type} [MetricSpace X] {s : Set X} (hcompact : IsCompact s) (hlocal : LocallyConnectedSpace s) : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by sorry
