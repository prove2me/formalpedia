-- Prove2me | Theorems.Thm_ThreeSum1960614_executable_scale_limits
-- name    : ThreeSum1960614.executable_scale_limits
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:33:50.371953+00:00
-- url     : https://prove2.me/theorems/ceee4e00-162f-4bb6-ab79-97d693159b35
-- title:
--   Limits of the actual rounded microblock, total size and band divisor
-- statement:
--   As the natural bit parameter $m$ tends to infinity, the executable schedules obey $s(m)^2/m\to0$, $\mu(m)/m\to e$, $a(m)/m\to(-b)e$, and $\log(2^{a(m)})/m\to\log(2)(-b)e$. Here $s,\mu,a$ are the actual integer cube-root and quotient schedules, $e=0.203889696$ and $b=-0.062656016$ are exact rationals, and logarithms are natural. The limits incorporate both integer rounding errors. They describe the changed schedule and its overhead scale, while the complete 3SUM program still requires separate operational contracts.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Section 4.1; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614 ThreeSum1960614.Schedule
open Filter
open scoped Topology

theorem ThreeSum1960614.executable_scale_limits :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 epsilon) ∧
    Tendsto (fun m : ℕ => (bandExponent m : ℝ) / m) atTop (𝓝 ((-beta) * epsilon)) ∧
    Tendsto (fun m : ℕ => Real.log (bandDivisor m : ℝ) / m) atTop
      (𝓝 (Real.log 2 * ((-beta) * epsilon)))  := by sorry
