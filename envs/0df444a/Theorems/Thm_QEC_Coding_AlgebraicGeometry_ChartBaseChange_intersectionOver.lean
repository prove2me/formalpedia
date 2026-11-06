-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionOver
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionOver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:45.949201+00:00
-- url     : https://prove2.me/theorems/402c8261-0f3a-4cef-b00a-a4b8f7ac1eec
-- title:
--   Chart Base Change: intersection Over
-- statement:
--   The Chart Base Change construction uses the intersection Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L37-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L37-L43

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

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionOver (h : IsPullback a b i j) :
    IsPullback (firstOverlapOver a i x) (secondOverlapOver a b i j x h)
      (leftChartOver i x) (rightChartOver j x) := by sorry
