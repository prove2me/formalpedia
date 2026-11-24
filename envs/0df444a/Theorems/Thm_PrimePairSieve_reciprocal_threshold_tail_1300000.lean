-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_threshold_tail_1300000
-- name    : PrimePairSieve.reciprocal_threshold_tail_1300000
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:22:17.749982+00:00
-- url     : https://prove2.me/theorems/b64d1a2a-ac0b-4407-9416-0133d7a504ce
-- title:
--   Reciprocal sieve threshold for every real z at least 1.3 million
-- statement:
--   For every real $z\ge1300000$, the mission's literal squarefree reciprocal sum satisfies
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}
--   \le\sum_{1\le n\le\lfloor z\rfloor}\frac{w(n)}{1+n/z},$$
--
--   where $C$ is the mission's twin-prime constant and $w(n)$ is zero for non-squarefree $n$, otherwise the product of $1$ at the prime 2 and $2/(p-2)$ at odd prime factors. The real variable, natural floor, and threshold are unchanged.
--
--   This refines the [already Proved tail above two million](https://prove2.me/theorems/bdbad104-76eb-4d51-a0f6-dab863c82475). It uses the same three accepted analytic inputs: the explicit quadratic expansion, second logarithmic moment bound, and sieve constants certificate. The improvement comes from retaining the sharper elementary constant-term bound $B\ge-47/20$, instead of rounding it down to $-3$. The existing inequalities give $B\ge-2.34943032\ge-47/20$.
--
--   For $z\ge1300000$, certify $\log z\ge14$ using $1250000=2^4 5^7$, and $z^{-1/3}\le1/109$ using $109^3\le1300000$. The logarithmic correction is bounded by $16^4/(25\cdot1300000)$. The exact rational comparison is
--
--   $$\frac{20.1732}{2.6434}-\frac{127185}{154\cdot109}
--   -\frac{16^4}{25\cdot1300000}>0.$$
--
--   The proof checks this comparison and its monotone extension to the entire unbounded interval in Lean. This is a formal numerical refinement of the existing argument, not a new sieve estimate. It shortens the finite certificate obligation; it does not by itself close the full reciprocal threshold or five-primes mission.
--
--   [Explicit expansion](https://prove2.me/theorems/19cc48fa-0e27-4d8a-af20-ebb90974f8d3), [second-moment bound](https://prove2.me/theorems/d2ad8149-27b5-4766-a7d8-f4492cfe28a1), [constants certificate](https://prove2.me/theorems/b2cb7da3-5535-4d4e-b75e-dfb1fa8e8a0d).
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_threshold_tail_1300000 :
    ∀ z : ℝ, 1300000 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry
