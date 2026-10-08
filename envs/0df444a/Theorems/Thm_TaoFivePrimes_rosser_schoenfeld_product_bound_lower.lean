-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_lower
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_lower
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-27T14:17:16.966719+00:00
-- url     : https://prove2.me/theorems/537dc0ba-c00a-474d-ba93-8e76a6ea85f0
-- title:
--   Rosser–Schoenfeld (1962): Mertens product lower bound $e^{\gamma}\log x < \prod_{p\le x} p/(p-1)$ on $2 \le x \le 10^8$
-- statement:
--   For every real $x$ with $2\le x\le 10^8$,
--
--   $$e^{\gamma}\,\log x\; < \;\prod_{p\le\lfloor x\rfloor,\;p\ \text{prime}}\frac{p}{p-1},$$
--
--   where the product runs over the primes $p\le\lfloor x\rfloor$ and $\gamma$ is the Euler--Mascheroni constant. Equivalently $\prod_{p\le x}(1-1/p) < e^{-\gamma}/\log x$.
--
--   **Source.** This is the lower half of the explicit Mertens-product estimate of J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. **6** (1962), 64--94. It is the companion of the upper half already on this platform as `TaoFivePrimes.rosser_schoenfeld_product_bound_to_1e8` ($\prod_{p\le x}p/(p-1) < e^{\gamma}\log x + 2e^{\gamma}/\sqrt{x}$, same range), whose own description explicitly names it as "the companion lower bound $e^{\gamma}\log x < \prod_{p\le x}p/(p-1)$" that that node omits. Secondary quotations: Y. Lamzouri, *A bias in Mertens' product formula*, arXiv:1410.3777, eq. (1.1), states it verbatim as "for all $2\le x\le 10^8$"; the zbMATH review of Diamond--Pintz (Zbl 1214.11102) renders the same 1962 calculation as $e^{-\gamma}/(\log x+2/\sqrt x) < \prod_{p\le x}(1-1/p) < e^{-\gamma}/\log x$ for $2\le x<10^8$.
--
--   **The range is essential -- do not strengthen this statement.** This is a *computational* verification carried out by Rosser and Schoenfeld up to $10^8$, not a theorem valid for all large $x$. Diamond and Pintz, *Oscillation of Mertens' product formula*, J. Theor. Nombres Bordeaux **21** (2009), 523--533, proved that
--   $$\sqrt{x}\Bigl(\prod_{p\le x}\tfrac{p}{p-1}-e^{\gamma}\log x\Bigr)$$
--   attains arbitrarily large positive and negative values, so the inequality genuinely fails for arbitrarily large $x$. A node asserting this beyond $10^8$ would be false.
--
--   **Independent numerical check performed for this node.** Sieving the primes to $2\cdot10^6$ and walking the product, the minimum of $\prod_{p\le n}p/(p-1)\,/\,(e^{\gamma}\log n)$ over primes $n\le 2\cdot10^6$ is $1.000021$, attained at $n=1772201$. The statement is true on the checked range but with a margin of only about $2\cdot10^{-5}$, i.e. it is close to tight; anyone using it should not expect room to spare.
--
--   **Role.** Together with the already-Proved `TaoFivePrimes.mertens_tail_le_partial_sum` it discharges the lower half of the Mawia reciprocal-prime estimate on the finite range: with $T(x)=\sum_{p\le x}(\log(1-1/p)+1/p)$ and $B=\gamma+\sum_p(\log(1-1/p)+1/p)$, the identity $\sum_{p\le x}1/p = \log\prod_{p\le x}\frac{p}{p-1} + T(x)$ turns this node plus $T(x)\ge T(\infty)$ into $\sum_{p\le x}1/p \ge \log\log x + B$.
--
--   This is a quoted external result; no reduction of it is proposed here.
-- source:
--   Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94: the calculation giving e^{-gamma}/(log x + 2/sqrt x) < prod_{p<=x}(1-1/p) < e^{-gamma}/log x for 2 <= x < 10^8. Lower half only, equivalently prod_{p<=x} p/(p-1) > e^{gamma} log x. Quoted as eq. (1.1) of Y. Lamzouri, A bias in Mertens' product formula, arXiv:1410.3777, with the range 2 <= x <= 10^8; and in the zbMATH review Zbl 1214.11102 of Diamond-Pintz. Valid only up to 10^8: Diamond-Pintz (2009) proved the difference changes sign infinitely often.

import Mathlib

namespace TaoFivePrimes

theorem rosser_schoenfeld_product_bound_lower (x : ℝ) (hx : 2 ≤ x) (hx' : x ≤ 10 ^ 8) :
    Real.exp Real.eulerMascheroniConstant * Real.log x <
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by
  sorry

end TaoFivePrimes
