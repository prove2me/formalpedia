-- Prove2me | Theorems.Thm_TaoFivePrimes_reciprocal_primes_theta_partial_summation
-- name    : TaoFivePrimes.reciprocal_primes_theta_partial_summation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:48:40.280354+00:00
-- url     : https://prove2.me/theorems/501826ec-ff1b-43a2-b74b-1477cd93d3b4
-- title:
--   Finite Abel summation for reciprocal primes and Chebyshev theta
-- statement:
--   For every real $x\ge2$, writing $\vartheta(t)=\sum_{p\le t}\log p$, finite Abel summation gives
--   $$\sum_{p\le x}\frac1p=\frac{\vartheta(x)}{x\log x}+\int_2^x\frac{\vartheta(t)(1+\log t)}{t^2\log^2t}\,dt.$$
--   This is an exact finite-interval identity: it uses no prime number theorem or numerical prime verification. Applying partial summation with weights $\log p$ and test function $1/(t\log t)$ proves it. It is the finite-interval input to the theta-tail remainder identity.
-- source:
--   Abel partial summation, specialized to f(t)=1/(t log t). See R. Vanlalngaia, Explicit Mertens Sums, Integers 17 (2017), A11, p. 9, proof preceding equation (17), https://emis.de/ft/19485.

import Mathlib

theorem TaoFivePrimes.reciprocal_primes_theta_partial_summation (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) / (x * Real.log x) +
      ∫ t in Set.Ioc (2 : ℝ) x,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by sorry
