-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_interval_certificate
-- name    : PrimePairSieve.reciprocal_base_denominator_interval_certificate
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T15:00:49.917052+00:00
-- url     : https://prove2.me/theorems/399f4fad-953d-4b94-880a-84fb162caaa7
-- title:
--   An endpoint certificate controls the reciprocal sieve threshold on a real interval
-- statement:
--   Let $S(z)$ be the literal reciprocal squarefree-weight denominator, with $w_2=1$, $w_p=2/(p-2)$ for odd primes and zero weight on nonsquarefree integers. For real endpoints $40\le L\le U$, choose a logarithm upper bound $\ell\ge\log(4U)$ and set $q_*=\ell^2/(5/2)$, $g_L=(L+1)/(16L^2)$. If $g_Lq_*<1$ and the endpoint certificate
--
--   $$\frac{q_*}{1-g_Lq_*}\le S(L)$$
--
--   holds, then the public reciprocal sieve threshold holds at every real $z\in[L,U]$. The theorem uses the existing certified lower bound $C\ge5/4$ for the twin-prime constant. It converts endpoint certificates into coverage of an entire real interval, including natural-floor jumps. It does not supply the individual numerical endpoint certificates.
-- source:
--   Reusable real-interval comparison underlying the exact-rational finite-window exploration in the five-primes mission. New formal consequence of nonnegative literal weights, natural-floor monotonicity, logarithm monotonicity and the Proved sieve_constants_certificate. No unproved finite-window assertion is imported.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

set_option autoImplicit false

theorem PrimePairSieve.reciprocal_base_denominator_interval_certificate
    (L U ell z : ℝ) (hL : 40 ≤ L) (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4 * U) ≤ ell)
    (hpositive : ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (5 / 2)) < 1)
    (hcertificate : ell ^ 2 / (5 / 2) /
        (1 - ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (5 / 2))) ≤
      ∑ q ∈ Finset.Icc 1 ⌊L⌋₊,
        (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / L)) :
    (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
        (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
          (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2))) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry
