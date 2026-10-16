-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_left_enclosure
-- name    : TaoFivePrimes.rh_batch01_height_vertical_center_left_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:42:37.463206+00:00
-- url     : https://prove2.me/theorems/4bab72bf-a1f6-4ad6-835a-acb1e2371b63
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_center_left_enclosure
-- statement:
--   All55 proposed center coefficients approximate the actual finite Fourier polynomial Taylor coefficients within2048e-18. Reuses checked accepted packet identities and checks the remaining exact packet identities directly with ordinary Lean kernel reduction, then applies the accepted analytic recurrence and exact-sum theorems. No boundary nonvanishing, winding, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalAnalyticValues

theorem TaoFivePrimes.rh_batch01_height_vertical_center_left_enclosure (n : Nat) (hn:n<55) :
 let p:=((RHBatch01VerticalCenterValuesLeft.values[n]?).getD (0,0))
 ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHBatch01VerticalAnalyticValues.center ⟨0,by decide⟩ n‖≤2048/10^18 := by sorry
