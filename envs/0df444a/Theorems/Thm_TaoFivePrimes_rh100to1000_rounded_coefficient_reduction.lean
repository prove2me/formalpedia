-- Prove2me | Theorems.Thm_TaoFivePrimes_rh100to1000_rounded_coefficient_reduction
-- name    : TaoFivePrimes.rh100to1000_rounded_coefficient_reduction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T06:04:07.04048+00:00
-- url     : https://prove2.me/theorems/437d601b-39fb-4b2b-ace1-e26724b593fa
-- title:
--   TaoFivePrimes.rh100to1000_rounded_coefficient_reduction
-- statement:
--   For any center |T|<=1000 and integral scale S<=10^350, certified errors of at most 10^-6 for the 272 scaled and rotated finite Mellin coefficient values imply that the corresponding rational rounded polynomial differs from S times xi by at most 1/100 on the closed unit disk. This conditional interface does not supply coefficient certificates or prove RH on a new height interval.
-- source:
--   Ordinary Lean continuation of sometik179's local xi Taylor and rounded polynomial method (original c9908072-d99a-4431-aad8-a72c6352619a); theta/Mellin foundations: Gabewhigham. Uses the accepted uniform finite xi polynomial error, finite norm sums, exact rotation by I, and rational error arithmetic.

import Definitions.Def_TaoFivePrimes_RH100To1000XiCoefficient
import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial

theorem TaoFivePrimes.rh100to1000_rounded_coefficient_reduction (T : ℝ) (hT : |T| ≤ 1000) (S : ℕ) (hS : S ≤ 10^350)
    (v : List ℤ)
    (hdata : ∀ n < 272, ‖(S:ℂ)*TaoFivePrimes_RH100To1000XiCoefficient T n*Complex.I^n-
      ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)‖ ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖(S:ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z‖ ≤ 1/100 := by sorry
