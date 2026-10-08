-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_error_transfer_bound
-- name    : PrimePairSieve.reciprocal_error_transfer_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T11:45:07.679345+00:00
-- url     : https://prove2.me/theorems/6f12c34b-74d3-461f-9064-f7b27feeca63
-- title:
--   Reciprocal sieve error transfer with a certified rational constant
-- statement:
--   Let $z>0$, $E\ge0$, and let $f$ be Lebesgue integrable on $(0,z]$ with
--
--   $$|f(t)|\le E t^{-1/3}\qquad(0<t\le z).$$
--
--   Then
--
--   $$\left|\frac{f(z)}2+\int_0^z\frac{z f(t)}{(z+t)^2}\,dt\right|\le\frac{8479}{6160}E z^{-1/3}.$$
--
--   This is the uniform error-transfer estimate for the reciprocal sieve kernel. The coefficient is $1/2+5399/6160$. It follows from a proved kernel bound and change of variables, and does not assert the sharp reciprocal denominator expansion or its $10/3$ error constant.
-- source:
--   Auxiliary integral and error bounds for the ordinary-to-reciprocal sieve denominator transfer discussed in the five-primes mission, comment ff52133e-299a-4b86-8771-c7b25bb01894 (2026-09-24), https://prove2.me/missions/Every_Odd_Number_Greater_Than_1_is_the_Sum_of_at_Most_Five_Primes. The logarithmic moment is classical; the stated rational bounds are independently derived polynomial certificates, not a quotation of Riesel and Vaughan. Context: Riesel and Vaughan, On sums of primes (1983), eqs. (3.6)-(3.10).

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
open MeasureTheory Set

theorem PrimePairSieve.reciprocal_error_transfer_bound (f : ℝ → ℝ) (z E : ℝ) (hz : 0 < z) (hE : 0 ≤ E)
    (hfint : IntegrableOn f (Set.Ioc 0 z))
    (hf : ∀ t ∈ Set.Ioc 0 z, |f t| ≤ E * t ^ (-(1 / 3 : ℝ))) :
    |f z / 2 + ∫ t in Set.Ioc 0 z, z / (z + t) ^ 2 * f t| ≤
      (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ)) := by sorry
