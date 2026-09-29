-- Prove2me | Theorems.Thm_Rudin_ch08_identity_theorem
-- name    : Rudin.ch08_identity_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:55:13.140238+00:00
-- url     : https://prove2.me/theorems/73cd5f5f-d77a-40bc-80c6-07831e91856a
-- title:
--   Theorem 8.5 — identity theorem for power series
-- statement:
--   If $\sum a_n x^n$ and $\sum b_n x^n$ converge on $(-R,R)$ and their sums agree on a set $E$ having a limit point in $(-R,R)$, then $a_n = b_n$ for all $n$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 177, Theorem 8.5

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.5: if two power series converge on `(-R, R)` and their sums agree on a set
which has a limit point in `(-R, R)`, then the two series have the same coefficients. -/
theorem ch08_identity_theorem (a b : ℕ → ℝ) (R : ℝ) (hR : 0 < R) (f g : ℝ → ℝ)
    (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => a n * x ^ n) (f x))
    (hg : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => b n * x ^ n) (g x))
    (E : Set ℝ) (hE : E ⊆ Set.Ioo (-R) R) (hagree : ∀ x ∈ E, f x = g x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (-R) R) (hlim : x₀ ∈ closure (E \ {x₀})) :
    ∀ n, a n = b n := by sorry

end Rudin
