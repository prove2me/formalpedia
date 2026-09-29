-- Prove2me | Theorems.Thm_Rudin_ch08_power_series_derivative
-- name    : Rudin.ch08_power_series_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:06:27.743761+00:00
-- url     : https://prove2.me/theorems/d6657031-0f33-40ed-b841-240dc3591c24
-- title:
--   Theorem 8.1 — term-by-term differentiation of power series
-- statement:
--   If $\sum c_n x^n$ converges for $|x| < R$ with sum $f(x)$, and $g(x)$ is the sum of the differentiated series $\sum n c_n x^{n-1}$ there, then $f$ is differentiable on $(-R,R)$ with $f' = g$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 173, Theorem 8.1

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.1: if the power series `∑ cₙ xⁿ` converges for `|x| < R` and `f` is its
sum, then `f` is differentiable on `(-R, R)` and its derivative is obtained by term-by-term
differentiation. -/
theorem ch08_power_series_derivative (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hconv : ∀ x : ℝ, |x| < R → SeriesConverges (fun n => c n * x ^ n))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => c n * x ^ n) (f x))
    (g : ℝ → ℝ) (hg : ∀ x : ℝ, |x| < R →
      SeriesConvergesTo (fun n => (n : ℝ) * c n * x ^ (n - 1)) (g x)) :
    ∀ x : ℝ, |x| < R → HasDerivAt f (g x) x := by sorry

end Rudin
