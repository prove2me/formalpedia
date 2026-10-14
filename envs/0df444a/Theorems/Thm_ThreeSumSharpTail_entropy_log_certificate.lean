-- Prove2me | Theorems.Thm_ThreeSumSharpTail_entropy_log_certificate
-- name    : ThreeSumSharpTail.entropy_log_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T16:30:41.27867+00:00
-- url     : https://prove2.me/theorems/4028af00-1260-4a15-b234-377dd2550b67
-- title:
--   Exact rational logarithm enclosures for the sharp-tail entropy arguments
-- statement:
--   Encloses the natural logarithms of 44399/1050000, 1005601/1050000, 5601/50000 and 44399/50000 between the exact rational endpoints in the statement. The first pair describes u=(1-0.11202)/21 and 1-u; the second describes theta=0.11202 and 1-theta. The bounds certify the sharp saving and query exponent. The proof reuses the log(2) bounds from the encoding logarithm certificate to scale all arguments into [1,2].
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Section 6.2; rational log-series certificate. Derived exact interval enclosures for the existing parameter certificate.

import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.entropy_log_certificate :
    ((-3163328497 / 10^9 : ℝ) ≤ Real.log (44399 / 1050000) ∧ Real.log (44399 / 1050000) ≤ -3163328495 / 10^9) ∧
    ((-43204792 / 10^9 : ℝ) ≤ Real.log (1005601 / 1050000) ∧ Real.log (1005601 / 1050000) ≤ -43204790 / 10^9) ∧
    ((-2189077853 / 10^9 : ℝ) ≤ Real.log (5601 / 50000) ∧ Real.log (5601 / 50000) ≤ -2189077851 / 10^9) ∧
    ((-118806060 / 10^9 : ℝ) ≤ Real.log (44399 / 50000) ∧ Real.log (44399 / 50000) ≤ -118806057 / 10^9) := by sorry
