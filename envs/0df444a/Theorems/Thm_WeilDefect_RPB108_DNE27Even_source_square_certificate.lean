-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_source_square_certificate
-- name    : WeilDefect.RPB108.DNE27Even.source_square_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:21.59638+00:00
-- url     : https://prove2.me/theorems/a0a6d32c-66b7-433e-93ec-d69282ba2bc2
-- title:
--   DNE27 even: source square certificate
-- statement:
--   Use the exact rational data of the even DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For each coordinate,
--
--   $$s_i\le[a(c_i-n_i)]^2.$$
--
--   This is an exact scalar certificate used with a separately supplied source norm bound. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27Numerics.lean#L31-L34; exact native declaration WeilDefect.RPB108.DNE27Even.source_square_certificate; SHA256 c34fd52113eac1864098b6f45aa0f69b8c323effeec75b12b71e5f49a7f7d6da. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.source_square_certificate (i : Fin 4) :
    sourceSquare i ≤ (highFloor*(completedMass i-nativeMass i))^2 := by sorry
