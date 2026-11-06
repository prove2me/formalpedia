-- Prove2me | Theorems.Thm_RH_Transport_Geometry_gram_margin_gt
-- name    : RH.Transport.Geometry.gram_margin_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:55:55.291145+00:00
-- url     : https://prove2.me/theorems/6c32a39d-df3a-4eee-ac6c-4d09c7df37cd
-- title:
--   Geometry: gram margin gt
-- statement:
--   The Geometry construction uses the gram margin gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L158-L163
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L158-L163

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.gram_margin_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (1 / 30 : ℝ) < ly p - d - 11 * b / 6 := by sorry
