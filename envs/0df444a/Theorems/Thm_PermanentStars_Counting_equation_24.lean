-- Prove2me | Theorems.Thm_PermanentStars_Counting_equation_24
-- name    : PermanentStars.Counting.equation_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:34.69419+00:00
-- url     : https://prove2.me/theorems/bb27067a-4680-4eac-9f57-53201b1cf8fd
-- title:
--   Section 5, equation (24) — Weighted binomial entropy bound
-- statement:
--   Let $n\ge0$ be an integer, let $1<c<2$, and let $0\le\alpha\le1/c$. Write $H$ for binary entropy with $H(0)=H(1)=0$. Then
--   $$\sum_{p=0}^{\lfloor\alpha n\rfloor}\binom np(c-1)^{-p}\le(n+1)2^{n(H(\alpha)-\alpha\log_2(c-1))}.$$
--   Both $\alpha=0$ and $n=0$ are included. The inherited condition on $c$ ensures the logarithm has a positive argument. This converts the nursery sum into the exponent used in the resource bound.
--
--   Differences from the source:
--   - encoding: binary entropy and real powers → Real.binEntropy/log 2, Real.rpow, and the nonnegative natural floor; reason: these are the same real functions on the source domain, including entropy endpoints
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Section 5, equation (24), PDF/printed p.11

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

/-- Section 5, (24), p.11, with its inherited 1<c<2 and including alpha=0. -/
theorem equation_24 (n : ℕ) (c a : ℝ) (hc : 1 < c) (hc2 : c < 2)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / c) :
    binomialBudget n a c ≤ (n + 1 : ℝ) *
      Real.rpow 2 ((n : ℝ) * (entropy a - a * (Real.log (c - 1) / Real.log 2))) := by sorry

end PermanentStars.Counting
