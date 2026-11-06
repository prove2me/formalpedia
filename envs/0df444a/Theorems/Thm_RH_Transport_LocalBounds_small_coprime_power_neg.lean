-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_small_coprime_power_neg
-- name    : RH.Transport.LocalBounds.small_coprime_power_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:06.512192+00:00
-- url     : https://prove2.me/theorems/5f703645-afaf-47fd-abdd-c67a6f2ac891
-- title:
--   Local Bounds: small coprime power neg
-- statement:
--   Exponents on the small-row contour, not bounds for the local factors.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L178-L182
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L178-L182

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.small_coprime_power_neg {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : PrincipalTerm) :
    principalPower term s (1 / 2) (17 / 50) < 0 := by sorry
