-- Prove2me | Theorems.Thm_Rudin_ch03_cauchy_criterion
-- name    : Rudin.ch03_cauchy_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:03:07.202264+00:00
-- url     : https://prove2.me/theorems/b8b43bf9-9ca8-4ec2-8001-5c50472828ca
-- title:
--   Theorem 3.22 — Cauchy criterion for series
-- statement:
--   A series $\sum a_n$ of complex numbers converges if and only if for every $\varepsilon > 0$ there is an $N$ such that $\left|\sum_{k=n}^{m} a_k\right| \le \varepsilon$ whenever $m \ge n \ge N$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 59, Theorem 3.22

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.22 (Cauchy criterion for series): `∑ aₙ` converges if and only if for every
`ε > 0` there is an integer `N` such that `‖∑_{k=n}^{m} aₖ‖ ≤ ε` whenever `m ≥ n ≥ N`. -/
theorem ch03_cauchy_criterion (a : ℕ → ℂ) :
    SeriesConverges a ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ n → n ≤ m →
        ‖∑ k ∈ Finset.Icc n m, a k‖ ≤ ε := by sorry

end Rudin
