-- Prove2me | Theorems.Thm_RH_Transport_Geometry_lx_residual_gt
-- name    : RH.Transport.Geometry.lx_residual_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:55:58.45441+00:00
-- url     : https://prove2.me/theorems/d66743c6-040d-4d3c-926c-7eeb367d046a
-- title:
--   Geometry: lx residual gt
-- statement:
--   The Geometry construction uses the lx residual gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L144-L149
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L144-L149

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.lx_residual_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (11 / 80 : ℝ) < lx p - d := by sorry
