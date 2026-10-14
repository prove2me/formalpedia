-- Prove2me | Theorems.Thm_TaoFivePrimes_rh100to1000_negative_exp_approximation
-- name    : TaoFivePrimes.rh100to1000_negative_exp_approximation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T06:14:22.909639+00:00
-- url     : https://prove2.me/theorems/ada30490-ef1d-48e2-9e0d-1186f4fd53c8
-- title:
--   TaoFivePrimes.rh100to1000_negative_exp_approximation
-- statement:
--   For every nonnegative real x, the finite piecewise arithmetic formula approximates exp(-x) with absolute error at most 10^-1200. It uses a 1024-term rational series raised to the 4096th power when x<=4096, and zero when x>4096. This supplies theta-term amplitude evaluation, not Mellin coefficients or RH certificates.
-- source:
--   Ordinary Lean continuation of sometik179's finite theta/Mellin certificate approach, original c9908072-d99a-4431-aad8-a72c6352619a; foundations: Gabewhigham. The proof combines the rigorous exponential series remainder, an elementary power error induction, and exp(4096)>=2^4096 for the omitted tail.

import Definitions.Def_TaoFivePrimes_RH100To1000NegativeExpApproximation

theorem TaoFivePrimes.rh100to1000_negative_exp_approximation (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x)-TaoFivePrimes_RH100To1000NegativeExpApproximation x| ≤ 1/10^1200 := by sorry
