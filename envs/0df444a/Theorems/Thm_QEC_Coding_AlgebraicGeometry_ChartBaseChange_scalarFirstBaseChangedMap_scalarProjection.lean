-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_scalarProjection
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_scalarProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:48.123397+00:00
-- url     : https://prove2.me/theorems/caf5075d-491f-4a24-a7c7-ef987adaa6c0
-- title:
--   Chart Base Change: scalar First Base Changed Map scalar Projection
-- statement:
--   The Chart Base Change construction uses the scalar First Base Changed Map scalar Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L67-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L67-L71

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

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_scalarProjection {A B : C}
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu ≫ pullback.fst t g = pullback.fst t f := by sorry
