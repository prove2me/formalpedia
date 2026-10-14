-- Prove2me | Theorems.Thm_ThreeSum1960614_log_coefficients
-- name    : ThreeSum1960614.log_coefficients
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:17:48.869982+00:00
-- url     : https://prove2.me/theorems/79325a7a-1b88-453b-867d-581dbb95566f
-- title:
--   Exact logarithmic certificate for four switch coefficients
-- statement:
--   The real natural logarithm of 2 lies between 0.693147180559945 and 0.693147180559946. The four exact rational quartic coefficients obey their respective derivative-series bounds: a1 log(2)<log(231), 2 a2 log(2)<=1+1/231, 3 a3 log(2)<=(1-1/231^2)/2, and 4 a4 log(2)<=(1+1/231^3)/3. These are unconditional exact real inequalities.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Sections 2–3; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.log_coefficients :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180559946 / 10^15 : ℝ) ∧
    (785174904 / 100000000 : ℝ) * Real.log 2 < Real.log 231 ∧
    (2 * 72447023 / 100000000 : ℝ) * Real.log 2 ≤ 1 + (1 / 231 : ℝ) ∧
    (3 * 24044466 / 100000000 : ℝ) * Real.log 2 ≤ (1 - (1 / 231 : ℝ) ^ 2) / 2 ∧
    (4 * 12022459 / 100000000 : ℝ) * Real.log 2 ≤ (1 + (1 / 231 : ℝ) ^ 3) / 3  := by sorry
