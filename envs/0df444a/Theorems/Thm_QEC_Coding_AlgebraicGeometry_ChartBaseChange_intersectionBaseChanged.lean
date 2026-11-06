-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChanged
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChanged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:48.016044+00:00
-- url     : https://prove2.me/theorems/d1d9f294-aa97-48c5-8608-fe97edc8c315
-- title:
--   Chart Base Change: intersection Base Changed
-- statement:
--   The Chart Base Change construction uses the intersection Base Changed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L54-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L54-L59

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C]
variable {P U V X Z T : C}
variable (a : P ⟶ U) (b : P ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
variable (x : X ⟶ Z) (t : T ⟶ Z)
variable [HasPullbacks C]

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChanged (h : IsPullback a b i j) :
    IsPullback (((Over.pullback t).map (firstOverlapOver a i x)).left)
      (((Over.pullback t).map (secondOverlapOver a b i j x h)).left)
      (((Over.pullback t).map (leftChartOver i x)).left)
      (((Over.pullback t).map (rightChartOver j x)).left) := by sorry
