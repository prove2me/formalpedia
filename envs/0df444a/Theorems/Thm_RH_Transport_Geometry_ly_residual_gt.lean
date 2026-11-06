-- Prove2me | Theorems.Thm_RH_Transport_Geometry_ly_residual_gt
-- name    : RH.Transport.Geometry.ly_residual_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:55:55.028086+00:00
-- url     : https://prove2.me/theorems/160e9ebe-9404-46f5-bbb8-049b88f6b9d0
-- title:
--   Geometry: ly residual gt
-- statement:
--   The Geometry construction uses the ly residual gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L151-L156
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L151-L156

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.ly_residual_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (21 / 80 : ℝ) < ly p - d := by sorry
