-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_good_cap_attained
-- name    : RH.Transport.LocalBounds.good_cap_attained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:56:17.607005+00:00
-- url     : https://prove2.me/theorems/1a8ebd7e-3ad4-4efc-a8bc-7e595ca42589
-- title:
--   Local Bounds: good cap attained
-- statement:
--   The grouped strict-family exponent attains the specified cap at the corner.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L90-L94
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L90-L94

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.good_cap_attained (p : ℝ) :
    goodPower .strictFamily (boundary p) (19 / 20) (33 / 200) =
      goodCap p := by sorry
