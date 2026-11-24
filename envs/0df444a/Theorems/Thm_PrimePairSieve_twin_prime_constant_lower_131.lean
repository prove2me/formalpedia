-- Prove2me | Theorems.Thm_PrimePairSieve_twin_prime_constant_lower_131
-- name    : PrimePairSieve.twin_prime_constant_lower_131
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:08:16.783986+00:00
-- url     : https://prove2.me/theorems/16f2d523-ba3d-4626-b137-e7973fee4b7b
-- title:
--   Certified lower bound 1.31 for the twin-prime singular constant
-- statement:
--   For the mission's normalization
--
--   $$C=2\inf_Q\prod_{2<p\le Q}\left(1-\frac1{(p-1)^2}\right),$$
--
--   this theorem proves $C\ge131/100$. This strengthens the lower bound $5/4$ used by the existing interval certificates; it is a numerical certification of a known constant, not a new number-theoretic estimate.
--
--   The proof adapts **andreaskapfer**'s accepted `sieve_constants_certificate`, submission `91b4ca4a-771c-4be3-88cd-952059ec7610`, using the same elementary telescoping comparison at cutoff 200. Lean kernel reduction checks that the finite product through 200 is at least $66/100$. The integer 201 is composite. For $Q\ge201$, the later partial product is at least the cutoff product times $200Q/(201(Q-1))$, hence at least $(66/100)(200/201)>655/1000$. Smaller partial products are larger than the cutoff product. Taking the infimum gives $C\ge2(655/1000)=131/100$.
--
--   The source imports only Mathlib and the published singular-series definition. Its successful local check reports only `propext`, `Classical.choice`, and `Quot.sound`. It does not import the old constants theorem as an assumption. The rational finite product and composite boundary are checked in Lean.
--
--   [Accepted source target](https://prove2.me/theorems/b2cb7da3-5535-4d4e-b75e-dfb1fa8e8a0d), [constant definition](https://prove2.me/theorems/061c3a0a-11a8-465a-b6ed-f595bb990c09).
-- source:
--   Formal refinement for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b. The mathematical argument and prior accepted source are described in the statement; no claim of a new analytic estimate.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.twin_prime_constant_lower_131 : (131/100 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant := by sorry
