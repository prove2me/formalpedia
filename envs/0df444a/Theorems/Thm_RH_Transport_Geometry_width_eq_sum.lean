-- Prove2me | Theorems.Thm_RH_Transport_Geometry_width_eq_sum
-- name    : RH.Transport.Geometry.width_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:59.465354+00:00
-- url     : https://prove2.me/theorems/b13f099b-8322-4ef7-b3f3-7beb9e82cea2
-- title:
--   Geometry: width eq sum
-- statement:
--   The Geometry construction uses the width eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L48-L50
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L48-L50

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.width_eq_sum (p : ℝ) : width p = lx p + ly p := by sorry
