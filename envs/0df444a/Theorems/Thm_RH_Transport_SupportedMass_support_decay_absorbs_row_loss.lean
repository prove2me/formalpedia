-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_support_decay_absorbs_row_loss
-- name    : RH.Transport.SupportedMass.support_decay_absorbs_row_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:50.74467+00:00
-- url     : https://prove2.me/theorems/5d3d6c3d-3963-4d47-8b2c-5dc9af463d21
-- title:
--   Supported Mass: support decay absorbs row loss
-- statement:
--   Absorbs the specified half-row loss against the support-derived half decay.
--   This does not assert that a row energy satisfies the specified loss formula.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L167-L183
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L167-L183

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.support_decay_absorbs_row_loss {p d Z mass C : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * Geometry.ell p - 1 + d) / 8) ≤ C := by sorry
