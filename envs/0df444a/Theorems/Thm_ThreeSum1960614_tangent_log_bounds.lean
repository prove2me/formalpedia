-- Prove2me | Theorems.Thm_ThreeSum1960614_tangent_log_bounds
-- name    : ThreeSum1960614.tangent_log_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:35:09.222154+00:00
-- url     : https://prove2.me/theorems/eb511634-dac7-447e-9fa7-9177b75c8cba
-- title:
--   Exact logarithmic bounds for the entropy supporting line
-- statement:
--   For the exact rational tangent point u=0.17200068185091493, the two real quantities -log(1-u)/log(2) and [-log(1-u)-log(u)]/[2 log(2)] are strictly below 0.272298515211 and 1.40590616299 respectively. These are the values at 0 and 1/2 of the binary-entropy tangent line, with all logarithms natural.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Sections 2–3; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.tangent_log_bounds :
    -Real.log (1 - tangentPoint) / Real.log 2 < (272298515211 / 1000000000000 : ℝ) ∧
    (-Real.log (1 - tangentPoint) - Real.log tangentPoint) / (2 * Real.log 2) <
      (140590616299 / 100000000000 : ℝ)  := by sorry
