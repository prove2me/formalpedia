-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChangedScalarFirst
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedScalarFirst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:13.498107+00:00
-- url     : https://prove2.me/theorems/531eca50-49ef-4931-bca2-f3a9c352e864
-- title:
--   Chart Base Change: intersection Base Changed Scalar First
-- statement:
--   The Chart Base Change construction uses the intersection Base Changed Scalar First property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L80-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L80-L93

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

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedScalarFirst (h : IsPullback a b i j) :
    IsPullback
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (i ≫ x) a rfl)
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (j ≫ x) b
        (by simpa only [Category.assoc] using congrArg (fun k => k ≫ x) h.w.symm))
      (scalarFirstBaseChangedMap t (i ≫ x) x i rfl)
      (scalarFirstBaseChangedMap t (j ≫ x) x j rfl) := by sorry
