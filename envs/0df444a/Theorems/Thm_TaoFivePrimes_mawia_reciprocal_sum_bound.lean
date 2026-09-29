-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound
-- name    : TaoFivePrimes.mawia_reciprocal_sum_bound
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-24T15:36:16.183128+00:00
-- url     : https://prove2.me/theorems/a182289a-f875-49fa-b946-9402fe0a3503
-- title:
--   Explicit Mertens sum: $\sum_{p\le x}1/p=\log\log x+B+O^*(4/\log^3 x)$ (Mawia 2017)
-- statement:
--   For every real $x\ge 2$,
--
--   $$\left|\sum_{p\le x}\frac1p-\log\log x-B\right|\;\le\;\frac{4}{\log^3 x},$$
--
--   where $B$ is the Meissel--Mertens constant, written here in the form our other nodes use,
--
--   $$B=\gamma+\sum_p\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr)=0.2614972\ldots,$$
--
--   $\gamma$ being the Euler--Mascheroni constant. Equivalently, in the notation of the source, $\sum_{p\le x}1/p=\log\log x+B+O^{*}(4/\log^{3}x)$, where $O^{*}$ means the error is bounded in **absolute value** by the stated quantity.
--
--   **Source.** R. Mawia (R. Vanlalngaia, Ramdinmawia), *Explicit Mertens sums*, 2017 (zbMATH Zbl 1412.11125), extending Rosser--Schoenfeld (1962) by the method of that paper. The statement above is the first of the three ranges tabulated for this theorem in the TME-EMT explicit-bounds wiki (*Explicit bounds on primes*, Art01, §2), which quotes it as: for $x\ge 2$, $\sum_{p\le x}1/p=\log\log x+B+O^{*}(4/\log^{3}x)$; when $x\ge1000$ the $4$ can be replaced by $2.3$, and when $x\ge24284$ by $1$. **This node states the first (widest-range, most generous) case**, which is the safest reading of the source and is already strong enough for everything that consumes it.
--
--   **Role.** This is the analytic input for the reciprocal-prime bounds and hence for the Mertens product bound (`rosser_schoenfeld_product_log_bound_large`). It is a *quoted external result*: no reduction of it is proposed here. It is deliberately stated with the constant $4$ over the full range $x\ge2$ rather than with the sharper constants available for larger $x$, so that any consumer gets a statement whose truth does not depend on the finer cases of the source.
--
--   **Why it supersedes the earlier plan.** A previous route attempted to derive $\sum_{p\le x}1/p$ bounds from the published Chebyshev input $|\psi(t)-t|\le t/(40\log t)$ by Abel summation. That cannot work: the identity $A_1(x)=(\vartheta(x)-x)/(x\log x)-\int_x^\infty(\vartheta(y)-y)(1+\log y)/(y^2\log^2 y)\,dy$ turns a $1/\log$ error into a $1/\log$ error in $A_1$ rather than a $1/\log^2$ one, and the two sides cross at $x=1.0668\cdot10^8$. A Chebyshev estimate with at least two powers of $\log$ in the denominator is needed instead, which is exactly the content of this node (via Mawia's explicit Mertens sums). See `missions/five-primes/A-star-route-audit.md` in the project repository.
-- source:
--   R. Mawia (R. Vanlalngaia, Ramdinmawia), Explicit Mertens sums, 2017; zbMATH Zbl 1412.11125. Statement as tabulated in the TME-EMT wiki, Explicit bounds on primes, Art01, section 2 (Mawia, 2017): for x >= 2, sum_{p<=x} 1/p = log log x + B + O*(4/log^3 x); for x >= 1000 the constant 4 may be replaced by 2.3, and for x >= 24284 by 1. Here B = gamma + sum_p (log(1-1/p) + 1/p) is the Meissel-Mertens constant, and O* denotes an absolute-value bound. This node states the widest-range case (constant 4).

import Mathlib

namespace TaoFivePrimes

theorem mawia_reciprocal_sum_bound (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  sorry

end TaoFivePrimes
