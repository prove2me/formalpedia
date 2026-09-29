-- Prove2me | Theorems.Thm_Rudin_ch10_partition_of_unity
-- name    : Rudin.ch10_partition_of_unity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:56:10.773761+00:00
-- url     : https://prove2.me/theorems/7978fdcb-3d66-4c2b-8d2d-a683e45442b6
-- title:
--   Theorem 10.8 — partitions of unity
-- statement:
--   Let $K$ be a compact subset of $\mathbb{R}^n$ covered by open sets $V_\alpha$. Then there are finitely many continuous functions $\psi_1,\dots,\psi_s$ with compact support, each supported in some $V_\alpha$, with $\psi_j \ge 0$, $\sum_j \psi_j = 1$ on $K$, and $\sum_j \psi_j \le 1$ everywhere.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 251, Theorem 10.8

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.8 (partitions of unity): if `K` is a compact subset of `ℝⁿ` covered by
open sets `V i`, there are finitely many continuous functions `ψ j` with compact support, each
supported in one of the `V i`, with `0 ≤ ψ j`, `∑ ψ j = 1` on `K` and `∑ ψ j ≤ 1`
everywhere. -/
theorem ch10_partition_of_unity (n : ℕ) (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (ι : Type) (V : ι → Set (Fin n → ℝ)) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ (s : ℕ) (ψ : Fin s → (Fin n → ℝ) → ℝ) (idx : Fin s → ι),
      (∀ j, Continuous (ψ j)) ∧ (∀ j, ∀ x, 0 ≤ ψ j x) ∧
      (∀ j, HasCompactSupport (ψ j)) ∧ (∀ j, tsupport (ψ j) ⊆ V (idx j)) ∧
      (∀ x ∈ K, ∑ j, ψ j x = 1) ∧ (∀ x, ∑ j, ψ j x ≤ 1) := by sorry

end Rudin
