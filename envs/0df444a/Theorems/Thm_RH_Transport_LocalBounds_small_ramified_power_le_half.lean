-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_small_ramified_power_le_half
-- name    : RH.Transport.LocalBounds.small_ramified_power_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:10.545768+00:00
-- url     : https://prove2.me/theorems/48aa4f86-fe3f-4c18-abaf-48f0313bf216
-- title:
--   Local Bounds: small ramified power le half
-- statement:
--   The Local Bounds construction uses the small ramified power le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L196-L200
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L196-L200

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.small_ramified_power_le_half {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : SmallRamifiedTerm) :
    smallRamifiedPower term s ≤ 1 / 2 := by sorry
