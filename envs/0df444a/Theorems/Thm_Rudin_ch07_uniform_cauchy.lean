-- Prove2me | Theorems.Thm_Rudin_ch07_uniform_cauchy
-- name    : Rudin.ch07_uniform_cauchy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:06:04.491631+00:00
-- url     : https://prove2.me/theorems/d1ee58ea-d1b9-4380-90b1-fd572fe5d2e6
-- title:
--   Theorem 7.8 — the uniform Cauchy criterion
-- statement:
--   A sequence of complex functions converges uniformly on $E$ if and only if for every $\varepsilon > 0$ there is $N$ such that $|f_n(x) - f_m(x)| \le \varepsilon$ for all $m, n \ge N$ and all $x \in E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 147, Theorem 7.8

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.8: a sequence of functions converges uniformly on `E` if and only if it
satisfies the uniform Cauchy criterion on `E`. -/
theorem ch07_uniform_cauchy {X : Type*} (E : Set X) (f : ℕ → X → ℂ) :
    (∃ g : X → ℂ, TendstoUniformlyOn f g atTop E) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ E, ‖f n x - f m x‖ ≤ ε := by sorry

end Rudin
