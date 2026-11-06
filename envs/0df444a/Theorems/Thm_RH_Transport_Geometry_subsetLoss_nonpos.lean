-- Prove2me | Theorems.Thm_RH_Transport_Geometry_subsetLoss_nonpos
-- name    : RH.Transport.Geometry.subsetLoss_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:29.607889+00:00
-- url     : https://prove2.me/theorems/287da48a-544c-4de2-ae1d-e1818938b863
-- title:
--   Geometry: subset Loss nonpos
-- statement:
--   Algebraic absorption on the actual subset-length interval.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L205-L210
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L205-L210

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.subsetLoss_nonpos {p d : ℝ}
    (_hp0 : 0 < p) (hp : p < 1 / 30)
    (hd0 : 0 ≤ d) (_hdell : d ≤ ell p) :
    subsetLoss p d ≤ 0 := by sorry
