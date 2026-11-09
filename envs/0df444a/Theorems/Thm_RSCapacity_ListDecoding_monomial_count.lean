-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_monomial_count
-- name    : RSCapacity.ListDecoding.monomial_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:50.51187+00:00
-- url     : https://prove2.me/theorems/0a70713d-4710-4fe6-ad54-70f0f3db5e16
-- title:
--   Fact 2.1 — number of weighted bivariate monomials
-- statement:
--   Let $k,D$ be positive integers and let $N(k,D)$ count the pairs of nonnegative integer exponents $(a,b)$ such that $a+kb<D$, equivalently the monomials $X^aY^b$ of weighted degree strictly below $D$. Then
--   $$\frac{D(D+k)}{2k}\le N(k,D)\le\frac{D(D+k)}{2k}+\frac{k}{8}.$$
--   Both inequalities, the strict cutoff, and the additive coefficient $1/8$ are retained. This provides the exact finite monomial-count estimate used in the interpolation bookkeeping.
--
--   Differences from the source: none.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Fact 2.1, p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Counting

namespace RSCapacity.ListDecoding

/-- Fact 2.1, submission #495 p.7. Both inequalities and the k/8 term. -/
theorem monomial_count (k D : ℕ) (hk : 0 < k) (hD : 0 < D) :
    (D : ℝ) * (D + k) / (2 * k) ≤ (bivariateMonomials k D).card ∧
    ((bivariateMonomials k D).card : ℝ) ≤
      (D : ℝ) * (D + k) / (2 * k) + (k : ℝ) / 8 := by sorry

end RSCapacity.ListDecoding
