-- Prove2me | Theorems.Thm_ThreeSum1960614_encoding_parameter_bounds
-- name    : ThreeSum1960614.encoding_parameter_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:17:18.045306+00:00
-- url     : https://prove2.me/theorems/a9706156-d570-4deb-9673-92dc5a793f2a
-- title:
--   Strict expansion-232 encoding and collision intervals
-- statement:
--   The fixed expansion-232 entropy constants obey 4.648781151243719 < E(232) < 4.648781151243720 and 0.001557987216578 < kappa(232) < 0.001557987216579, with E and kappa defined in the shared analytic bundle. All four displayed endpoints are exact rationals with denominator 10^15.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Sections 5.1 and 8, exact_interval.py; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.encoding_parameter_bounds :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000  := by sorry
