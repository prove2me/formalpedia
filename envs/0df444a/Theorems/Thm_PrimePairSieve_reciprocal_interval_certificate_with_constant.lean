-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_interval_certificate_with_constant
-- name    : PrimePairSieve.reciprocal_interval_certificate_with_constant
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:08:32.526981+00:00
-- url     : https://prove2.me/theorems/4823a11b-a486-4768-a3f7-e7cf3d50fccf
-- title:
--   Reciprocal interval criterion with a certified constant parameter
-- statement:
--   Let $C$ be the mission's twin-prime constant and let $c_0$ be any positive certified lower bound for $C$. For $40\le L\le U$, choose $\ell\ge\log(4U)$, put $q_*=\ell^2/(2c_0)$ and $g_L=(L+1)/(16L^2)$, and suppose $g_Lq_*<1$.
--
--   If the endpoint reciprocal sum is at least $q_*/(1-g_Lq_*)$, then the original reciprocal threshold holds at every real $z\in[L,U]$. The sum retains the literal squarefree weights and the natural-floor cutoff.
--
--   The proof generalizes the existing interval criterion, replacing its fixed lower bound $5/4$ by the explicit parameter $c_0$. The reciprocal sum increases with $z$, while $(z+1)/(16z^2)$ decreases. Logarithm monotonicity and $c_0\le C$ bound the numerator by $q_*$. The positive correction assumption then permits the two denominator comparisons. Nonnegative omitted terms handle the floor jumps.
--
--   The result does not establish a lower bound for $C$ or an endpoint certificate: those are explicit inputs. It lets independently certified improvements in the constant reduce the numerical work without changing the original threshold. The local proof is closed, using only Mathlib and the singular-series definition; its reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
--
--   [Existing fixed-constant criterion](https://prove2.me/theorems/399f4fad-953d-4b94-880a-84fb162caaa7).
-- source:
--   Formal refinement for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b. The mathematical argument and prior accepted source are described in the statement; no claim of a new analytic estimate.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_interval_certificate_with_constant
    (c₀ L U ell z : ℝ) (hc₀ : 0 < c₀) (hC : c₀ ≤ TaoFivePrimes.twinPrimeConstant) (hL : 40 ≤ L) (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4 * U) ≤ ell)
    (hpositive : ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (2*c₀)) < 1)
    (hcertificate : ell ^ 2 / (2*c₀) /
        (1 - ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (2*c₀))) ≤
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
