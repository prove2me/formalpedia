-- Prove2me | Theorems.Thm_TaoFivePrimes_five_primes_below_analytic_threshold
-- name    : TaoFivePrimes.five_primes_below_analytic_threshold
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-22T03:46:48.919071+00:00
-- url     : https://prove2.me/theorems/d02aaff7-3f39-4cd2-8879-76e24b8d715e
-- title:
--   Five primes below the analytic threshold $87\cdot10^{35}$
-- statement:
--   Every odd $n$ with $1 < n < 87\cdot10^{35}$ is a sum of at most five primes.
--
--   This is the range the circle-method argument of the mission does not reach. `TaoFivePrimes.three_primes_near` requires $x \ge 87\cdot10^{35}$ and `TaoFivePrimes.liu_wang_three_primes` requires $n \ge e^{3100}$, so together with this statement the odd numbers are covered with no gap, and `TaoFivePrimes.five_primes` follows.
--
--   **The intended proof: peel primes off the top, then finish with verified Goldbach.** Two inputs already present in this mission do it. `TaoFivePrimes.prime_in_short_interval` says that for $x \ge 1.1\cdot10^{10}$ there is a prime $p \le x$ with
--   $$x - p \;\le\; \frac{x}{2.8\cdot10^{7}},$$
--   and `TaoFivePrimes.even_goldbach_verified` says every even number in $[4,\, 4\cdot10^{14}]$ is a sum of two primes. Starting from $n$ and applying the first three times,
--   $$n \;<\; 8.7\cdot10^{36} \;\longmapsto\; 3.11\cdot10^{29} \;\longmapsto\; 1.11\cdot10^{22} \;\longmapsto\; 3.97\cdot10^{14},$$
--   and $3.97\cdot10^{14} < 4\cdot10^{14}$, so the remainder after three peels lies in the verified Goldbach range and contributes two more primes: five in all.
--
--   **The threshold is exactly this computation.** $4\cdot10^{14}\cdot(2.8\cdot10^{7})^{3} = 8.78\cdot10^{36}$, and the hypothesis $n < 87\cdot10^{35} = 8.7\cdot10^{36}$ sits just under it, with about one percent to spare. So the constant $87\cdot10^{35}$ appearing in `three_primes_near` and `representationCount_pos` is not an arbitrary convenience: it is the largest round threshold from which three applications of the Ramaré--Saouter gap bound still land inside the Goldbach verification. A fourth peel is not available, because `prime_in_short_interval` needs $x \ge 1.1\cdot10^{10}$ and the third remainder is already below the point where a further peel would help.
--
--   **Parity is what makes the count come out at five.** $n$ is odd and the peeled primes are odd (each is close to a number far larger than $2$), so the remainders alternate even, odd, even: the third remainder is even, which is what the Goldbach input requires. Peeling only twice would leave an odd remainder and no way to finish in two primes.
--
--   **Small cases.** Below the range where peeling applies the statement is immediate rather than special: for odd $7 \le n \le 4\cdot10^{14}+3$, the number $n-3$ is even and at most $4\cdot10^{14}$, so $n = 3 + p + q$ is a sum of three primes; and $n = 3, 5$ are themselves prime. The genuinely open content is therefore the middle range, where the number of peels needed varies with the size of $n$ and the hypothesis $x \ge 1.1\cdot10^{10}$ of the short-interval input has to be checked at each step.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656, Section 1 (the reduction of the small range); Ramare and Saouter, Short effective intervals containing primes, J. Number Theory 98 (2003); Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace TaoFivePrimes

theorem five_primes_below_analytic_threshold (n : ℕ) (hodd : Odd n) (hn : 1 < n)
    (hsmall : n < 87 * 10 ^ 35) :
    ∃ s : Multiset ℕ, s.card ≤ 5 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry

end TaoFivePrimes
