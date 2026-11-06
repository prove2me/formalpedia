-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleRestriction_cast
-- name    : QEC.Coding.AlgebraicGeometry.schemeModuleRestriction_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:32.137473+00:00
-- url     : https://prove2.me/theorems/d687118b-bddc-46c1-928f-059cd597ad2b
-- title:
--   Algebraic Geometry: scheme Module Restriction cast
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Restriction cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L234-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L234-L239

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]

theorem QEC.Coding.AlgebraicGeometry.schemeModuleRestriction_cast (M : X.Modules) {W V U : X.Opens}
    (e : W = V) (h : V ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (eqToHom e).op (M.presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE (e.le.trans h)).op s := by sorry
