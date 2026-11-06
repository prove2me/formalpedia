-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialImageSectionIsoTo_inv_global
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialImageSectionIsoTo_inv_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:18.571489+00:00
-- url     : https://prove2.me/theorems/f225605c-b01f-4696-8181-c48f67b724d4
-- title:
--   Algebraic Geometry: scheme Differential Image Section Iso To inv global
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Image Section Iso To inv global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L253-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L253-L263

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialImageSectionIsoTo_inv_global
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
    (h : schemeRestrictionConstantMap f k c = d)
    (s : Γ(schemeDifferentialSheaf X k c, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo f k c d h ⊤).inv
      ((schemeDifferentialSheaf X k c).presheaf.map
        (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    schemeDifferentialGlobalRestrictionTo f k c d h s := by sorry
