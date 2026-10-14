-- Prove2me | Theorems.Thm_ThreeSum1960614_high_precision_logs
-- name    : ThreeSum1960614.high_precision_logs
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:11:24.510651+00:00
-- url     : https://prove2.me/theorems/de7fe647-8aac-4316-94bf-b5004b38aa98
-- title:
--   Six logarithmic intervals with exact 22-digit rational endpoints
-- statement:
--   Certifies both endpoints of six exact rational intervals for the natural logarithms of 2, 29/16, 232/231, 464/463, 32 theta, and 2(1-theta), where theta=0.040409899 is the published fixed parameter. Every interval has denominator 10^22 and width 10^(-22). The endpoints are exactly those displayed in the formal statement; no rounding or numerical oracle is a hypothesis.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Sections 5.1 and 8, exact_interval.py; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.high_precision_logs :
    ((6931471805599453094172 / 10 ^ 22 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599453094173 / 10 ^ 22) ∧
    ((5947071077466927895143 / 10 ^ 22 : ℝ) ≤ Real.log (29 / 16) ∧
      Real.log (29 / 16) ≤ 5947071077466927895144 / 10 ^ 22) ∧
    ((43196611445164148724 / 10 ^ 22 : ℝ) ≤ Real.log (232 / 231) ∧
      Real.log (232 / 231) ≤ 43196611445164148725 / 10 ^ 22) ∧
    ((21574981400211907723 / 10 ^ 22 : ℝ) ≤ Real.log (464 / 463) ∧
      Real.log (464 / 463) ≤ 21574981400211907724 / 10 ^ 22) ∧
    ((2570554035235070921259 / 10 ^ 22 : ℝ) ≤ Real.log (32 * theta) ∧
      Real.log (32 * theta) ≤ 2570554035235070921260 / 10 ^ 22) ∧
    ((6518981167335747474116 / 10 ^ 22 : ℝ) ≤ Real.log (2 * (1 - theta)) ∧
      Real.log (2 * (1 - theta)) ≤ 6518981167335747474117 / 10 ^ 22)  := by sorry
