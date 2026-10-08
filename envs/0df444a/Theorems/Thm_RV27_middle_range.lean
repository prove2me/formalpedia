-- Prove2me | Theorems.Thm_RV27_middle_range
-- name    : RV27.middle_range
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T14:36:05.532929+00:00
-- url     : https://prove2.me/theorems/6cf38a61-32f2-4b6e-b562-da1790b72b34
-- title:
--   Sums of two odd primes have density at least 1/25 for $23 \le \log n \le 300$
-- statement:
--   Let $r(s)$ be the number of ordered pairs $(p,q)$ of odd primes with $p+q=s$ (platform definition `Schnir.r`). For every natural number $n$ with $23 \le \log n \le 300$,
--
--   $$
--   \#\{\, s \le n : r(s) > 0 \,\} \;\ge\; \frac{n}{25},
--   $$
--
--   where $s$ ranges over $\{0,1,\dots,n\}$.
--
--   This is the middle range of an explicit Schnirelmann argument for the bound $27$ on the number of primes needed to write an odd number. It follows Riesel and Vaughan's small-shift argument: with $Q$ the first $150$ odd primes and $R(s)=\#\{a\in Q : s-a \text{ an odd prime}\}$, Cauchy–Schwarz gives $\#\{s\le n: R(s)>0\}\ge (\sum R)^2/\sum R^2$. The first moment uses Chebyshev's bound $\psi(x)\ge 0.9212x-5\log x+5$; the second moment is bounded by Siebert's prime-pair bound $8C\,K(d)\,x/\log^2x$ with $K(d)=\prod_{p\mid d,\,p>2}\frac{p-1}{p-2}$ (platform theorem `TaoFivePrimes.siebert_prime_pair_bound`).
--
--   **Formalization Note** $\log$ is the natural logarithm `Real.log` of $n$ cast to $\mathbb{R}$; the count is the cardinality of the filter of `Finset.range (n + 1)`.
-- source:
--   H. Riesel, R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983), 45-74, Lemma 8 (small-shift Cauchy-Schwarz) and Lemma 5 (Siebert prime-pair bound); constants re-derived with Chebyshev psi(x) >= 0.9212x - 5 log x + 5 (PrimeNumberTheoremAnd IEANTN/Chebyshev.lean) in place of Rosser-Schoenfeld (unpublished AI-assisted calculation, October 2026).

import Mathlib
import Definitions.Def_Schnir_defs

namespace RV27

theorem middle_range (n : ℕ) (h1 : 23 ≤ Real.log (n : ℝ)) (h2 : Real.log (n : ℝ) ≤ 300) :
    (n : ℝ) / 25 ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by
  sorry

end RV27
