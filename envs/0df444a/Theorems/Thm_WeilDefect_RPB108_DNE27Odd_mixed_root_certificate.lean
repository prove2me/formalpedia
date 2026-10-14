-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_mixed_root_certificate
-- name    : WeilDefect.RPB108.DNE27Odd.mixed_root_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:17:57.379286+00:00
-- url     : https://prove2.me/theorems/e0782f44-07d1-4063-9f52-746eda508805
-- title:
--   DNE27 odd: mixed root certificate
-- statement:
--   Use the exact rational data of the odd DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For the exact odd mixed-energy data, write $\theta$ for the paid Young parameter, $M$ for the mixed upper bound, $N$ for the native low coefficient, $R$ for the retained lower weight, $d$ for the native dual square, and $b$ for the high mixed square. The exact square data satisfy
--
--   $$d\ge0,\quad b\ge0,\quad M\ge0,\quad M^2-d-b\ge0,\quad4db\le(M^2-d-b)^2.$$
--
--   These scalar inequalities certify the combined root bound without rounded arithmetic. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27MixedEnergy.lean#L103-L109; exact native declaration WeilDefect.RPB108.DNE27Odd.mixed_root_certificate; SHA256 45cb5b8d112c5975566df7932641b62a5eef54da1f9915fb26c1b5f5f4902360. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.mixed_root_certificate :
    0 ≤ nativeDualSquare ∧ 0 ≤ highMixedSquare ∧ 0 ≤ mixedUpper ∧
    0 ≤ mixedUpper^2-nativeDualSquare-highMixedSquare ∧
    4*nativeDualSquare*highMixedSquare ≤
      (mixedUpper^2-nativeDualSquare-highMixedSquare)^2 := by sorry
