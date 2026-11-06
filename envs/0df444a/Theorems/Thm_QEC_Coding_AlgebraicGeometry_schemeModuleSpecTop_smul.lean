-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleSpecTop_smul
-- name    : QEC.Coding.AlgebraicGeometry.schemeModuleSpecTop_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:32.586347+00:00
-- url     : https://prove2.me/theorems/6de657a1-1351-44a2-8102-fdafcf73db1d
-- title:
--   Algebraic Geometry: scheme Module Spec Top smul
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Spec Top smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L265-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L265-L270

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u

theorem QEC.Coding.AlgebraicGeometry.schemeModuleSpecTop_smul (A : CommRingCat.{u}) (M : (Spec A).Modules)
    (a : A) (s : Γ(M, ⊤)) : a • s = (Scheme.ΓSpecIso A).inv a • s := by sorry
