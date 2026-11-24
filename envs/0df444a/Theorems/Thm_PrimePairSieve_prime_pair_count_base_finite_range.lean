-- Prove2me | Theorems.Thm_PrimePairSieve_prime_pair_count_base_finite_range
-- name    : PrimePairSieve.prime_pair_count_base_finite_range
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T13:10:10.216148+00:00
-- url     : https://prove2.me/theorems/45c0c3e7-5ebe-471b-b986-cdd00ae26b3d
-- title:
--   Prime-pair bound for the base case, verified for all x at most 25600
-- statement:
--   ## Statement
--
--   For all natural numbers $x,d$ with
--   $$2\le x\le 25600,\qquad d>0,\qquad 2\mid d,$$
--   the number of prime pairs with gap $d$ up to $x$ satisfies
--   $$\#\{n:\ n\ \text{prime},\ n+d\ \text{prime},\ n+d\le x\}
--   \ \le\ 8\,C\cdot\frac{x}{\log^2 x}\cdot\prod_{\substack{p\mid d\\ p>2}}\frac{p-1}{p-2},$$
--   where $C$ is the twin-prime singular constant.
--
--   ## Meaning
--
--   This is the finite-range part of the reduction of the target `TaoFivePrimes.siebert_prime_pair_bound`, whose statement allows all $x\ge 2$. The asymptotic range $x\ge 25600$ is handled by the sieve bound `PrimePairSieve_prime_pair_count_base_reciprocal_bound` (platform node) combined with the sharp reciprocal base-denominator expansion `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp`; the present statement supplies the complementary range $x<25600$.
--
--   A direct exact computation over all $x\le 25600$ and all even $d<25600$ shows that the ratio
--   $$\frac{\#\{n:\ n,n+d\ \text{prime},\ n+d\le x\}}{8C\,x\log^{-2}x\prod_{p\mid d,\,p>2}\frac{p-1}{p-2}}$$
--   attains its maximum $0.291$ at $(x,d)=(389,6)$ (and $0.203$ on the worst one-dimensional family $d=2^k$), so the inequality is true with a factor $>3$ to spare.
--
--   ## Proof route
--
--   For $x\ge 600$ (say) use the platform node `PrimePairSieve_prime_pair_count_base_reciprocal_bound` together with rational lower bounds for the finite sum $\sum_{q\le z,\ q\ \mathrm{squarefree}} b(q)$, e.g. monotonicity in $z$ plus the tabulated exact values of $\sum_{q\le m} b(q)$ for $m\le \lfloor\sqrt{x}/4\rfloor\le 40$; this already beats the target with $\ge 15\%$ margin in the whole range $600\le x\le 25600$. For $x<600$ the counts are tiny and can be certified by a finite computation; in both cases the required logarithmic bounds are rational and can be certified by the same certificate style used in `Thm_TaoFivePrimes_theta_cert_tables`.
--
--   ## Reference
--
--   Reduction step for the target `TaoFivePrimes.siebert_prime_pair_bound` (finite range, by exhaustive certification); compare H. Riesel and R. C. Vaughan, *On sums of primes*, Ark. Mat. **21** (1983), 46--74.
-- source:
--   Finite-range reduction step for TaoFivePrimes.siebert_prime_pair_bound; exhaustive certification.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

namespace PrimePairSieve

theorem prime_pair_count_base_finite_range (x d : ℕ) (hx : 2 ≤ x) (hx0 : x ≤ 25600)
    (hd0 : 0 < d) (hd : 2 ∣ d) :
    (∑ n ∈ Finset.range (x + 1),
      if Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x then (1 : ℝ) else 0) ≤
      8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
        ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by sorry

end PrimePairSieve
