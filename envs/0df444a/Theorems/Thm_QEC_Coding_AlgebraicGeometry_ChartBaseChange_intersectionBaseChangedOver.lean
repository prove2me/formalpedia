-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChangedOver
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedOver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:46.364194+00:00
-- url     : https://prove2.me/theorems/3d6361eb-4a6c-4e8c-b001-541241062d0a
-- title:
--   Chart Base Change: intersection Base Changed Over
-- statement:
--   The Chart Base Change construction uses the intersection Base Changed Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L47-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L47-L52

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

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedOver (h : IsPullback a b i j) :
    IsPullback ((Over.pullback t).map (firstOverlapOver a i x))
      ((Over.pullback t).map (secondOverlapOver a b i j x h))
      ((Over.pullback t).map (leftChartOver i x))
      ((Over.pullback t).map (rightChartOver j x)) := by sorry
