-- Prove2me | Theorems.Thm_RH_Transport_Geometry_subsetLoss_le_linear
-- name    : RH.Transport.Geometry.subsetLoss_le_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:24.469205+00:00
-- url     : https://prove2.me/theorems/17af0d3f-18b0-41f6-ad77-9d8bb67739f6
-- title:
--   Geometry: subset Loss le linear
-- statement:
--   The Geometry construction uses the subset Loss le linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L197-L202
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L197-L202

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.subsetLoss_le_linear {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    subsetLoss p d ≤ -(7 / 8 : ℝ) * d := by sorry
