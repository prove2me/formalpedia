-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_eq_pullbackMap
-- name    : QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_eq_pullbackMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:19.007557+00:00
-- url     : https://prove2.me/theorems/5f4b5d78-5c87-429f-8f66-b98d93a21a15
-- title:
--   Chart Base Change: scalar First Base Changed Map eq pullback Map
-- statement:
--   The Chart Base Change construction uses the scalar First Base Changed Map eq pullback Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L103-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean#L103-L111

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
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B Z T : C} (t : T ⟶ Z)

theorem QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_eq_pullbackMap
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu =
      pullback.map t f t g (𝟙 T) u (𝟙 Z) (by simp)
        (by simpa only [Category.comp_id] using hu.symm) := by sorry
