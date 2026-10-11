-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_mixed_root_certificate
-- name    : WeilDefect.RPB108.DNE27Even.mixed_root_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:52.900211+00:00
-- url     : https://prove2.me/theorems/11d8657d-e86f-49a7-bbf5-b0d17c0ae833
-- title:
--   DNE27 even: mixed root certificate
-- statement:
--   Use the exact rational data of the even DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For the exact even mixed-energy data, write $\theta$ for the paid Young parameter, $M$ for the mixed upper bound, $N$ for the native low coefficient, $R$ for the retained lower weight, $d$ for the native dual square, and $b$ for the high mixed square. The exact square data satisfy
--
--   $$d\ge0,\quad b\ge0,\quad M\ge0,\quad M^2-d-b\ge0,\quad4db\le(M^2-d-b)^2.$$
--
--   These scalar inequalities certify the combined root bound without rounded arithmetic. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27MixedEnergy.lean#L25-L31; exact native declaration WeilDefect.RPB108.DNE27Even.mixed_root_certificate; SHA256 45cb5b8d112c5975566df7932641b62a5eef54da1f9915fb26c1b5f5f4902360. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.

import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.mixed_root_certificate :
    0 ≤ nativeDualSquare ∧ 0 ≤ highMixedSquare ∧ 0 ≤ mixedUpper ∧
    0 ≤ mixedUpper^2-nativeDualSquare-highMixedSquare ∧
    4*nativeDualSquare*highMixedSquare ≤
      (mixedUpper^2-nativeDualSquare-highMixedSquare)^2 := by sorry
