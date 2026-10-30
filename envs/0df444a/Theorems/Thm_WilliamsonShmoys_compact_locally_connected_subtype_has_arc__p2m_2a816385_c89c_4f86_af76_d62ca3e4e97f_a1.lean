-- Prove2me | Theorems.Thm_WilliamsonShmoys_compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
-- name    : WilliamsonShmoys.compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:31.228046+00:00
-- url     : https://prove2.me/theorems/e413f8c6-3436-44b7-927c-9061da113dbc
-- title:
--   Compact locally connected plane sets contain arcs
-- statement:
--   In a compact, locally connected, path-connected subset of the plane, any two distinct points can be joined by an injective continuous curve contained in the set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1 {s : Set (ℝ × ℝ)} (hcompact : IsCompact s) (hpath : IsPathConnected s) (hlocal : LocallyConnectedSpace s) (a b : s) (hne : a ≠ b) : ∃ φ : ℝ → ℝ × ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ Set.InjOn φ (Set.Icc 0 1) ∧ φ 0 = a.val ∧ φ 1 = b.val ∧ (∀ t ∈ Set.Icc 0 1, φ t ∈ s) := by sorry
