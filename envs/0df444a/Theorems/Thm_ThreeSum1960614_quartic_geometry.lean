-- Prove2me | Theorems.Thm_ThreeSum1960614_quartic_geometry
-- name    : ThreeSum1960614.quartic_geometry
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:17:45.083499+00:00
-- url     : https://prove2.me/theorems/5eadf13c-7877-4753-a08c-3cf8eba024a4
-- title:
--   Quartic derivative and tangent geometry
-- statement:
--   For every real t in the closed interval [0,1/2], the exact expansion-232 quartic has derivative strictly between 0 and 9, and its tangent at the fixed rational point 0.17200068185091493 lies below it. Both endpoints are included. The explicit polynomial and derivative are supplied by the shared analytic definitions.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Sections 2–3; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.quartic_geometry (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t  := by sorry
