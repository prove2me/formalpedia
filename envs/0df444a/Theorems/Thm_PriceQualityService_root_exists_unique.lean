-- Prove2me | Theorems.Thm_PriceQualityService_root_exists_unique
-- name    : PriceQualityService.root_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:39:51.085824+00:00
-- url     : https://prove2.me/theorems/86ccc7cc-6af6-418b-aa38-6f9c7b3bca2a
-- title:
--   Proof of Theorem 1, p. 27 — the root $r^*$ of the pricing equation exists and is unique
-- statement:
--   Let $N\ge 0$ and let $w_1,\dots,w_N$ be real numbers. There is exactly one real number $r$ with
--
--   $$
--   r=\sum_{i=1}^{N}\exp(w_i-r-1).
--   $$
--
--   The left side increases and the right side strictly decreases in $r$. The root is the optimal profit of the price-optimized problem: eq. (17) at fixed qualities and durations, eq. (19) after optimizing the durations, and eqs. (24)–(25) in the uniform-duration problem.
--
--   Differences from the source:
--   - generalization: the unique solution of equation (19), whose exponents are max_{t_i} of the exponent of (17) → every exponent vector w : Fin N → ℝ; reason: the argument (left side increasing, right side strictly decreasing) does not use the form of w; (19) is the instance w_i = max_{t_i}(…)
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 27 (unnumbered, after eq. (19)); also Theorem 1(c), p. 10

import Mathlib

namespace PriceQualityService

/-- **The root `r*` of the pricing equation exists and is unique.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), unnumbered, p. 27: "Note that `H(r)` is a strictly decreasing
function w.r.t. r. Denote the unique solution to equation (19) by `r*`."

For every exponent vector `w` there is exactly one real `r` with
`r = Σ_i exp(w_i − r − 1)`.

**Formalization Note.** The paper says this for equation (19), whose exponents are
`w_i = max_{t_i}` of the exponent of (17). The statement here is for every vector `w`, which
covers (17) at fixed `(q, t)`, (19), and (24)/(25). For `N = 0` the root is `0`. -/
theorem root_exists_unique {N : ℕ} (w : Fin N → ℝ) :
    ∃! r : ℝ, r = ∑ i, Real.exp (w i - r - 1) := by sorry

end PriceQualityService
