-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_endpoint_log_error
-- name    : TaoFivePrimes.rh_high_height_contour_endpoint_log_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:31:36.446862+00:00
-- url     : https://prove2.me/theorems/00373306-f942-433c-9191-63dce8d3b5bc
-- title:
--   TaoFivePrimes.rh_high_height_contour_endpoint_log_error
-- statement:
--   For actual polynomial endpoint values within1e-12 of the proposed80-bit values, native center magnitude at least1e-4 and endpoint ratio within1/2, the actual principal logarithm of the endpoint ratio differs from the ordinary128-bit rounded16-term logarithm by at most1e-4. Proves division rounding, logarithm polynomial rounding, perturbation and analytic Taylor remainder. No winding, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourArithmetic
import Definitions.Def_TaoFivePrimes_RHHighContourVector

theorem TaoFivePrimes.rh_high_height_contour_endpoint_log_error (c v : Int×Int) (A B : ℂ)
 (hM:0<RHHighContourArithmetic.normSq c)
 (hc:(1/10000:ℝ)≤‖RHHighContourVector.value c‖)
 (hA:‖A-RHHighContourVector.value c‖≤1/10^12)
 (hB:‖B-RHHighContourVector.value v‖≤1/10^12)
 (hr:‖RHHighContourVector.value v/RHHighContourVector.value c-1‖≤1/2) :
 let p:=RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)
 ‖Complex.log (B/A)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128‖≤1/10000 := by sorry
