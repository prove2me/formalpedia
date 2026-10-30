-- Prove2me | Theorems.Thm_WilliamsonShmoys_compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1
-- name    : WilliamsonShmoys.compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:35.041712+00:00
-- url     : https://prove2.me/theorems/de9ec37e-3877-485c-a882-6cad68becd14
-- title:
--   Compact locally connected metric sets contain arcs
-- statement:
--   In a compact, locally connected, path-connected subset of any metric space, any two distinct points can be joined by a continuous injective parametrized arc contained in the subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1 {X : Type} [MetricSpace X] {s : Set X} (hcompact : IsCompact s) (hpath : IsPathConnected s) (hlocal : LocallyConnectedSpace s) (a b : s) (hne : a ≠ b) : ∃ φ : ℝ → X, ContinuousOn φ (Set.Icc 0 1) ∧ Set.InjOn φ (Set.Icc 0 1) ∧ φ 0 = a.val ∧ φ 1 = b.val ∧ (∀ t ∈ Set.Icc 0 1, φ t ∈ s) := by sorry
