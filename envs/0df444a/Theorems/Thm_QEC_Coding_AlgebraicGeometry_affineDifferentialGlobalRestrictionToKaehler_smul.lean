-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionToKaehler_smul
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionToKaehler_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:54.066499+00:00
-- url     : https://prove2.me/theorems/a8a74cf2-4a9f-41b8-af94-a6be5d937175
-- title:
--   Algebraic Geometry: affine Differential Global Restriction To Kaehler smul
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Restriction To Kaehler smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L290-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L290-L307

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u})
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
attribute [local instance] QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalConstantModule
variable (A : CommRingCat.{u}) [Algebra k A] (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "psi" => schemeDifferentialGlobalRestrictionTo f (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) hf

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionToKaehler_smul (r : k) (s : Γ(OmegaX, ⊤)) :
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf (r • s) =
      r • affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by sorry
