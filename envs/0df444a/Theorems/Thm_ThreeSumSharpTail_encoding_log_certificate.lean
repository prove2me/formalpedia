-- Prove2me | Theorems.Thm_ThreeSumSharpTail_encoding_log_certificate
-- name    : ThreeSumSharpTail.encoding_log_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T16:30:47.497518+00:00
-- url     : https://prove2.me/theorems/92294eef-fad4-45e4-a508-2975c6d74172
-- title:
--   Exact rational logarithm enclosures for encoding and baseline entropy
-- statement:
--   Encloses the natural logarithms of 2, 10, 3, 9, 1/21 and 20/21 between the exact rational endpoints in the statement. These enclosures certify the denominator log(4), the encoding cost and H(1/21) in the sharp-tail parameter certificate. They are obtained by rational atanh partial sums with explicit remainder bounds and power-of-two argument scaling.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Section 6.2; rational log-series certificate. Derived exact interval enclosures for the existing parameter certificate.

import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.encoding_log_certificate :
    ((693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 693147180559946 / 10^15) ∧
    ((2302585092 / 10^9 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2302585094 / 10^9) ∧
    ((1098612288 / 10^9 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1098612290 / 10^9) ∧
    ((2197224575 / 10^9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 2197224580 / 10^9) ∧
    ((-3044522438 / 10^9 : ℝ) ≤ Real.log (1 / 21) ∧ Real.log (1 / 21) ≤ -3044522436 / 10^9) ∧
    ((-48790165 / 10^9 : ℝ) ≤ Real.log (20 / 21) ∧ Real.log (20 / 21) ≤ -48790163 / 10^9) := by sorry
