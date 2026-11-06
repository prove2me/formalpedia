-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_denominator_power_neg
-- name    : RH.Transport.LocalBounds.denominator_power_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:56:15.12908+00:00
-- url     : https://prove2.me/theorems/7eab9df8-db3b-4a52-8969-6aaa4d3dfc7f
-- title:
--   Local Bounds: denominator power neg
-- statement:
--   The Local Bounds construction uses the denominator power neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L49-L53
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L49-L53

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.denominator_power_neg {p s z : ℝ} (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hz : (33 / 200 : ℝ) ≤ z)
    (term : DenominatorTerm) : denominatorPower term s z < 0 := by sorry
