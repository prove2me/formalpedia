-- Prove2me | Theorems.Thm_ThreeSumSharpTail_encoding_bound
-- name    : ThreeSumSharpTail.encoding_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:10:55.91583+00:00
-- url     : https://prove2.me/theorems/3b79d171-3aa3-478e-b660-5e9673953c1f
-- title:
--   Encoding cost bound from the binomial entropy certificate
-- statement:
--   For every integer c>10 and m>=1, the encoding factor 10^(cm)/sqrt(M) is at most sqrt(cm+1) times (4^m)^A(c), where M is the exact baseline box count choose(cm,m)*9^(cm-m). This is the pointwise encoding inequality used to show eventual tile fit and absorb preprocessing overheads. The proof uses the lower binomial entropy bound and exact exponential algebra; it makes no program-runtime conclusion by itself.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Section 4, equation encodingbound.

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.encoding_bound (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m) :
    (10 : ℝ) ^ (c * m) / Real.sqrt (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      Real.sqrt (c * m + 1 : ℝ) * (4 ^ m : ℝ) ^ ThreeSumSharpTail.encodingExponent c := by sorry
