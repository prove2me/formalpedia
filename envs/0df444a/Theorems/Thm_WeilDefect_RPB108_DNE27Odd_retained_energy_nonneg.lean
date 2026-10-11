-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_energy_nonneg
-- name    : WeilDefect.RPB108.DNE27Odd.retained_energy_nonneg
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:39.67837+00:00
-- url     : https://prove2.me/theorems/e06255ca-81b5-4f7e-8620-b7ba46d2f973
-- title:
--   DNE27 odd: retained energy nonneg
-- statement:
--   Use the exact rational data of the odd DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For the exact odd mixed-energy data, write $\theta$ for the paid Young parameter, $M$ for the mixed upper bound, $N$ for the native low coefficient, $R$ for the retained lower weight, $d$ for the native dual square, and $b$ for the high mixed square. For $z\in\mathbb C^4$, define $\mathcal R(z)=R\sum_{j=1}^3|z_j|^2$. Then
--
--   $$\mathcal R(z)\ge0.$$
--
--   This justifies the real square root appearing in the mixed-energy estimate. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27MixedEnergy.lean#L124-L126; exact native declaration WeilDefect.RPB108.DNE27Odd.retained_energy_nonneg; SHA256 45cb5b8d112c5975566df7932641b62a5eef54da1f9915fb26c1b5f5f4902360. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.

import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.retained_energy_nonneg (z : Fin 4 → ℂ) : 0 ≤ retainedEnergy z := by sorry
