-- Prove2me | Theorems.Thm_ThreeSum1960614_quartic_parameter_certificate
-- name    : ThreeSum1960614.quartic_parameter_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:08:07.48987+00:00
-- url     : https://prove2.me/theorems/6f7c52c1-6e2d-4554-adb3-bf79b8ed51a9
-- title:
--   Exact parameters and all twelve cost caps
-- statement:
--   The expansion-232 entropy and multiplicity constants satisfy $4.648781151243719<E_{232}<4.648781151243720$ and $0.001557987216578<\kappa_{232}<0.001557987216579$, while $H(\theta)<0.244168414687344$. The initial threshold is below $P(\theta)$, the terminal threshold is below $P(1/2)$, and $0<e(E_{232}+b)<1$. Every one of the twelve exact real costs is strictly below $1.96061388<1.960614$. These inequalities assert an analytic certificate and do not themselves assert a machine runtime.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Section 5.1; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.quartic_parameter_certificate :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 ∧
    entropy theta < 244168414687344 / 1000000000000000 ∧
    v < phi theta ∧ threshold tau < phi (1 / 2) ∧
    0 < epsilon * (E 232 + beta) ∧ epsilon * (E 232 + beta) < 1 ∧
    (∀ z ∈ costs, z < principal) ∧ principal < (target : ℝ) := by sorry
