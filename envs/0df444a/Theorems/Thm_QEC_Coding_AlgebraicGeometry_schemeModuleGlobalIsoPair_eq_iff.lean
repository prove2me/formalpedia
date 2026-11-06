-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleGlobalIsoPair_eq_iff
-- name    : QEC.Coding.AlgebraicGeometry.schemeModuleGlobalIsoPair_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:58:51.83036+00:00
-- url     : https://prove2.me/theorems/98ffafb7-8bdd-442d-b57a-461d3e864fed
-- title:
--   Algebraic Geometry: scheme Module Global Iso Pair eq iff
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Global Iso Pair eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L121-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L121-L134

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)

theorem QEC.Coding.AlgebraicGeometry.schemeModuleGlobalIsoPair_eq_iff (z : Γ(M, ⊤)) (a : A) (b : B) :
    schemeModuleGlobalIsoPair M U V e f z = (a, b) ↔
    M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = e.inv a ∧
      M.presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = f.inv b := by sorry
