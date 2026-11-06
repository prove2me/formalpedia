-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_principal_power_le
-- name    : RH.Transport.LocalBounds.principal_power_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:32.161911+00:00
-- url     : https://prove2.me/theorems/9db2ae79-3d37-406f-b060-103b4d61e495
-- title:
--   Local Bounds: principal power le
-- statement:
--   The Local Bounds construction uses the principal power le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L148-L153
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L148-L153

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.principal_power_le {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -boundary p := by sorry
