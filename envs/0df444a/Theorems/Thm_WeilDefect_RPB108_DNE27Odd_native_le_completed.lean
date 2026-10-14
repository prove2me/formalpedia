-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_native_le_completed
-- name    : WeilDefect.RPB108.DNE27Odd.native_le_completed
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:16:32.826016+00:00
-- url     : https://prove2.me/theorems/e19344cb-62b1-4183-90f3-34bd4c2b18d2
-- title:
--   DNE27 odd: native le completed
-- statement:
--   Use the exact rational data of the odd DNE27 input bundle. Coordinates are indexed by $i\in\{0,1,2,3\}$. Write $L_i$ for the lower weights, $n_i$ for native masses, $c_i$ for completed masses, $s_i$ for source-square bounds, $a=11/25$ for the high floor, and $\delta=4/10^{36}$. For each coordinate,
--
--   $$n_i\le c_i.$$
--
--   This compares the exact native and completed mass inputs. The four coordinates are retained directions, not a zeta-zero quartet. This result does not establish RH, the complete 1.06 positivity theorem or global continuation.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27Numerics.lean#L79-L80; exact native declaration WeilDefect.RPB108.DNE27Odd.native_le_completed; SHA256 c34fd52113eac1864098b6f45aa0f69b8c323effeec75b12b71e5f49a7f7d6da. Generated rational inputs are custodially pinned; this theorem proves their scalar relations or a conditional norm-space specialization. Original-form realizations and upstream analytic/interval-producer replay are separate tasks.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.native_le_completed (i : Fin 4) : nativeMass i ≤ completedMass i := by sorry
