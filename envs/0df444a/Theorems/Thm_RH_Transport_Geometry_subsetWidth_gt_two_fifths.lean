-- Prove2me | Theorems.Thm_RH_Transport_Geometry_subsetWidth_gt_two_fifths
-- name    : RH.Transport.Geometry.subsetWidth_gt_two_fifths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:55:55.473212+00:00
-- url     : https://prove2.me/theorems/47805c13-30b2-4487-a1d8-7f82f481db5b
-- title:
--   Geometry: subset Width gt two fifths
-- statement:
--   The Geometry construction uses the subset Width gt two fifths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L132-L137
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L132-L137

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.subsetWidth_gt_two_fifths {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (2 / 5 : ℝ) < subsetWidth p d := by sorry
