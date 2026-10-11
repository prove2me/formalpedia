-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_denominator_guard
-- name    : WeilDefect.RPB108.DNE27Even.denominator_guard
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:29.747977+00:00
-- url     : https://prove2.me/theorems/020e0f1b-5b74-4368-9d7a-3ef1daa88a2b
-- title:
--   DNE27 even: denominator guard
-- statement:
--   Use the exact rational data of the even DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. The weighted denominator satisfies
--
--   $$\delta\left(\sum_{i=0}^3\frac{c_i^2}{L_i}+\frac1a\right)\le1.$$
--
--   This certifies the scalar guard in the conditional physical-gap estimate. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27Numerics.lean#L36-L39; exact native declaration WeilDefect.RPB108.DNE27Even.denominator_guard; SHA256 c34fd52113eac1864098b6f45aa0f69b8c323effeec75b12b71e5f49a7f7d6da. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.

import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.denominator_guard :
    gap * ((∑ i, (completedMass i)^2/lower i)+1/highFloor) ≤ 1 := by sorry
