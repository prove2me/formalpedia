-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_mixed_diagonal_lower
-- name    : WeilDefect.RPB108.DNE27Even.mixed_diagonal_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:34.162922+00:00
-- url     : https://prove2.me/theorems/89c4403e-2c84-4e13-b18a-6056fb80b72e
-- title:
--   DNE27 even: mixed diagonal lower
-- statement:
--   Use the exact rational data of the even DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For the exact even mixed-energy data, write $\theta$ for the paid Young parameter, $M$ for the mixed upper bound, $N$ for the native low coefficient, $R$ for the retained lower weight, $d$ for the native dual square, and $b$ for the high mixed square. For $z\in\mathbb C^4$, define $\mathcal R(z)=R\sum_{j=1}^3|z_j|^2$. Then
--
--   $$\sum_i L_i|z_i|^2\le N|z_0|^2-2M|z_0|\sqrt{\mathcal R(z)}+\mathcal R(z).$$
--
--   This compares the certified diagonal lower form to the mixed-energy expression. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27MixedEnergy.lean#L50-L60; exact native declaration WeilDefect.RPB108.DNE27Even.mixed_diagonal_lower; SHA256 45cb5b8d112c5975566df7932641b62a5eef54da1f9915fb26c1b5f5f4902360. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.

import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.mixed_diagonal_lower (z : Fin 4 → ℂ) :
    (∑ i, lower i*‖z i‖^2) ≤
      nativeLow*‖z 0‖^2-2*mixedUpper*(‖z 0‖*Real.sqrt (retainedEnergy z)) +
        retainedEnergy z := by sorry
