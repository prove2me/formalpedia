-- Prove2me | Theorems.Thm_ThreeSum1960614_quartic_switch_bounds
-- name    : ThreeSum1960614.quartic_switch_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:07:04.730278+00:00
-- url     : https://prove2.me/theorems/8223bf4a-1f91-47b9-a6a5-d332ecdb806d
-- title:
--   Quartic switch validity on the full half interval
-- statement:
--   For every real $0\le t\le1/2$, the exact quartic satisfies $P(t)\le\gamma_{232}(t)$ and $0<P'(t)<9$. Its tangent at $u=0.17200068185091493$ lies below $P(t)$ throughout the same interval. Both endpoints are included; the conclusion concerns the whole continuum.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Sections 2–3; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.quartic_switch_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t ∧ 0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by sorry
