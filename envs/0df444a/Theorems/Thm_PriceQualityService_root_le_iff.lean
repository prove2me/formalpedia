-- Prove2me | Theorems.Thm_PriceQualityService_root_le_iff
-- name    : PriceQualityService.root_le_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:53.28832+00:00
-- url     : https://prove2.me/theorems/0f216725-1d28-41a7-94e7-7b9bc594c633
-- title:
--   Eq. (25) — the root is increasing in the aggregate attraction $\sum_i e^{w_i}$
-- statement:
--   Let $w,w'\in\mathbb R^N$ and let $r,r'$ be real numbers with
--
--   $$
--   r=\sum_{i}\exp(w_i-r-1),\qquad r'=\sum_{i}\exp(w'_i-r'-1).
--   $$
--
--   Then
--
--   $$
--   r\le r'\iff\sum_i e^{w_i}\le\sum_i e^{w'_i}.
--   $$
--
--   Rewriting the root equation as $r\,e^{1+r}=\sum_ie^{w_i}$ is eq. (25): the root depends on the exponents only through the numerator $y=\sum_ie^{w_i}$, and is increasing in it. This is why maximizing the profit over durations amounts to maximizing $y$.
--
--   Differences from the source:
--   - generalization: exponents of eq. (24) (the uniform-duration problem at the unconstrained optimal quality) → arbitrary exponent vectors w, w'; reason: the monotonicity argument does not use the form of the exponents; (25) is the instance
--   - encoding: "the optimization problem in terms of t is only related to the numerator of the RHS"; LHS increasing, RHS strictly decreasing in r → r ≤ r' ↔ Σ exp(w_i) ≤ Σ exp(w'_i) for the two roots; reason: the comparison of two roots is the content of the quoted sentences, in both directions
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), eq. (25), p. 29, and p. 30

import Mathlib

namespace PriceQualityService

/-- **Eq. (25): the root is increasing in the aggregate attraction.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), eq. (25), p. 29 and p. 30: "equation (24) can be rewritten as
follows: `r = max_t Σ_{i∈𝒩} exp(b_i²t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i))t + α_i²/(4c_i)) / exp(1 + r)`
… We observe that the optimization problem in terms of t is only related to the numerator of the
RHS for any r > 0. … because the LHS of equation (25) is a linear increasing line and the RHS is
strictly decreasing in r."

If `r = Σ_i exp(w_i − r − 1)` and `r' = Σ_i exp(w'_i − r' − 1)`, then
`r ≤ r' ↔ Σ_i exp(w_i) ≤ Σ_i exp(w'_i)`: the root of (25) depends on the exponents only through
the numerator `y = Σ_i exp(w_i)`, and is increasing in it.

**Formalization Note.** Stated for arbitrary exponent vectors `w, w'`; the paper's instance is
`w_i` the exponent of (24) without `− r − 1`. -/
theorem root_le_iff {N : ℕ} (w w' : Fin N → ℝ) (r r' : ℝ)
    (hr : r = ∑ i, Real.exp (w i - r - 1)) (hr' : r' = ∑ i, Real.exp (w' i - r' - 1)) :
    r ≤ r' ↔ ∑ i, Real.exp (w i) ≤ ∑ i, Real.exp (w' i) := by sorry

end PriceQualityService
