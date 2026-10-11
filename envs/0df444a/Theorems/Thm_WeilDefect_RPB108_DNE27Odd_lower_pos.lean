-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_lower_pos
-- name    : WeilDefect.RPB108.DNE27Odd.lower_pos
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:17:13.935866+00:00
-- url     : https://prove2.me/theorems/5367623d-7ea9-472e-9380-d11c900ffa37
-- title:
--   DNE27 odd: lower pos
-- statement:
--   Use the exact rational data of the odd DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. All four lower energy weights are positive:
--
--   $$L_i>0.$$
--
--   This verifies the strict denominator condition for the finite weighted energy estimate. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27Numerics.lean#L76-L77; exact native declaration WeilDefect.RPB108.DNE27Odd.lower_pos; SHA256 c34fd52113eac1864098b6f45aa0f69b8c323effeec75b12b71e5f49a7f7d6da. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.

import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.lower_pos (i : Fin 4) : 0 < lower i := by sorry
