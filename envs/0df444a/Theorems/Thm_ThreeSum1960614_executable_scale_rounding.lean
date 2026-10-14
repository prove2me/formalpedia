-- Prove2me | Theorems.Thm_ThreeSum1960614_executable_scale_rounding
-- name    : ThreeSum1960614.executable_scale_rounding
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:26:44.23325+00:00
-- url     : https://prove2.me/theorems/bb028ec9-fde8-44b5-95aa-5450b036437f
-- title:
--   Exact finite rounding of the executable block and band schedules
-- statement:
--   For every natural bit parameter $m$, the executable even microblock size $s(m)$ is divisible by two and the block count $J(m)$ by twenty. Whenever $s(m)>0$, the exact total size obeys $0\le e m-\mu(m)<20s(m)$. For every $m$, including the zero-size fallback, the natural band exponent $a(m)$ obeys $0\le(-b)\mu(m)-a(m)<1$, and the divisor $2^{a(m)}$ is positive. Here $e=0.203889696$ and $b=-0.062656016$ are the fixed exact rational parameters. These are finite statements about actual natural-number quotients, without asymptotic hypotheses.
-- source:
--   Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Section 4.1; certificate c232_quartic.json; 14 October 2026.

import Definitions.Def_ThreeSum1960614_Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614 ThreeSum1960614.Schedule

theorem ThreeSum1960614.executable_scale_rounding (m : ℕ) :
    2 ∣ microSize m ∧ 20 ∣ blockCount m ∧
    (0 < microSize m →
      0 ≤ epsilon * (m : ℝ) - totalSize m ∧
      epsilon * (m : ℝ) - totalSize m < 20 * microSize m) ∧
    0 ≤ (-beta) * (totalSize m : ℝ) - bandExponent m ∧
    (-beta) * (totalSize m : ℝ) - bandExponent m < 1 ∧
    0 < bandDivisor m  := by sorry
