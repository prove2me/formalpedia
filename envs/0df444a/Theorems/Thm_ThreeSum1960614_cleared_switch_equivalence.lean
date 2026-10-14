-- Prove2me | Theorems.Thm_ThreeSum1960614_cleared_switch_equivalence
-- name    : ThreeSum1960614.cleared_switch_equivalence
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T06:39:25.379424+00:00
-- url     : https://prove2.me/theorems/d7521312-d5b4-4a10-9ef3-e1f391791b04
-- title:
--   Integer quartic comparison is exactly the analytic threshold test
-- statement:
--   For arbitrary natural J,s,j,q with J>0, s>0 and j<J, the published clearedSwitch integer comparison holds if and only if P(q/((J-j)s)) is at least (v+j/J)/(1-j/J), with v=159243801/500000000 and the exact quartic P. There is no restriction on q beyond being a natural number. The positive-depth hypothesis identifies real subtraction with truncated natural subtraction and makes all cleared denominators positive.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Section 4.2, comparison (I); certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.cleared_switch_equivalence (J s j q : ℕ) (hJ : 0 < J) (hs : 0 < s) (hj : j < J) :
    clearedSwitch J s j q ↔
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s))  := by sorry
