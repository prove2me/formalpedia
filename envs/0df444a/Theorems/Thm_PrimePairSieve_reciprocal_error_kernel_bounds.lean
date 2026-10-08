-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_error_kernel_bounds
-- name    : PrimePairSieve.reciprocal_error_kernel_bounds
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T11:44:58.858127+00:00
-- url     : https://prove2.me/theorems/f0083f19-72c7-49b5-95fc-bf0e363079d5
-- title:
--   Certified rational bounds for the reciprocal error kernel
-- statement:
--   Let
--
--   $$J=\int_0^1\frac{t^{-1/3}}{(1+t)^2}\,dt.$$
--
--   Then the following rational bounds hold:
--
--   $$\frac{6529}{7480}\le J\le\frac{5399}{6160}.$$
--
--   The bounds come from explicit rational polynomial minorants and majorants for $(1+t)^{-2}$ on $[0,1]$, followed by exact power integrals. They imply $1.3728609\ldots\le 1/2+J\le1.3764611\ldots$. The decimals are explanatory; the formal bounds are exact rationals. This certifies a transfer constant substantially below $3/2$ without relying on numerical quadrature.
-- source:
--   Auxiliary integral and error bounds for the ordinary-to-reciprocal sieve denominator transfer discussed in the five-primes mission, comment ff52133e-299a-4b86-8771-c7b25bb01894 (2026-09-24), https://prove2.me/missions/Every_Odd_Number_Greater_Than_1_is_the_Sum_of_at_Most_Five_Primes. The logarithmic moment is classical; the stated rational bounds are independently derived polynomial certificates, not a quotation of Riesel and Vaughan. Context: Riesel and Vaughan, On sums of primes (1983), eqs. (3.6)-(3.10).

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
open MeasureTheory Set

theorem PrimePairSieve.reciprocal_error_kernel_bounds :
    (6529 / 7480 : ℝ) ≤ (∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-(1 / 3 : ℝ)) / (1 + x) ^ 2) ∧
    (∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-(1 / 3 : ℝ)) / (1 + x) ^ 2) ≤ (5399 / 6160 : ℝ) := by sorry
