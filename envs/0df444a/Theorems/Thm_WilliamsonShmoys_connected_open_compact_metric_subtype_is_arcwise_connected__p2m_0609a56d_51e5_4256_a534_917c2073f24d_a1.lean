-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1
-- name    : WilliamsonShmoys.connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:54.311465+00:00
-- url     : https://prove2.me/theorems/3404bc54-276a-455b-b0dc-6dc075e5ae87
-- title:
--   Connected open subsets of compact locally connected metric spaces are arcwise connected
-- statement:
--   In a compact subset of a metric space that is locally connected as a subtype, every connected relatively open subset admits an arc from a fixed point to each distinct point, with the arc staying in that open subset. Compactness supplies local compactness; openness lets the subset inherit local connectedness and local compactness. The connected locally connected locally compact metrizable arc-connectedness theorem then gives a route to prove the claim.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1 {X : Type} [MetricSpace X] {s : Set X} (hcompact : IsCompact s) [LocallyConnectedSpace s] {V : Set s} (hVopen : IsOpen V) (hVconnected : IsConnected V) (x : s) (hxV : x ∈ V) : ∀ y : s, y ∈ V → y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ V := by sorry
