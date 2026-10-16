-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_right_enclosure
-- name    : TaoFivePrimes.rh_high_height_vertical_center_right_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T12:37:48.007981+00:00
-- url     : https://prove2.me/theorems/6ca55e38-cbb3-46e2-8fdd-0e299bf6e6b6
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_right_enclosure
-- statement:
--   All55 proposed center coefficients approximate the actual finite Fourier polynomial Taylor coefficients within2048e-18. Reuses checked accepted packet identities and checks the remaining exact packet identities directly with ordinary Lean kernel reduction, then applies the accepted analytic recurrence and exact-sum theorems. No boundary nonvanishing, winding, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalAnalyticValues

theorem TaoFivePrimes.rh_high_height_vertical_center_right_enclosure (n : Nat) (hn:n<55) :
 let p:=((RHHighVerticalCenterValuesRight.values[n]?).getD (0,0))
 ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHHighVerticalAnalyticValues.center ⟨2,by decide⟩ n‖≤2048/10^18 := by sorry
