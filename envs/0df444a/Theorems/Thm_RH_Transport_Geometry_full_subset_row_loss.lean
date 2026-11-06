-- Prove2me | Theorems.Thm_RH_Transport_Geometry_full_subset_row_loss
-- name    : RH.Transport.Geometry.full_subset_row_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:56:06.40201+00:00
-- url     : https://prove2.me/theorems/c6e51329-3cd3-4991-a9b2-00a6f51b9e3b
-- title:
--   Geometry: full subset row loss
-- statement:
--   At the fully rescaled subset, the specified row-energy loss before
--   Cauchy--Schwarz is 3p/2. This is only a formula evaluation.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L222-L229
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L222-L229

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.full_subset_row_loss {p : ℝ} (hp : 0 < p) :
    max 0 (5 * ell p - 1 + ell p) / 4 = 3 * p / 2 := by sorry
