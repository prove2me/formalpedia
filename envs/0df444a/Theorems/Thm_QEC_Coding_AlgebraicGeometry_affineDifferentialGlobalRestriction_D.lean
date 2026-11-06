-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestriction_D
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestriction_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:27.340423+00:00
-- url     : https://prove2.me/theorems/9dfd8492-5fb8-4da8-a39d-132dc166c63b
-- title:
--   Algebraic Geometry: affine Differential Global Restriction D
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Restriction D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L88-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L88-L100

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
local notation "f" => Spec.map q
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "cB" => affineDifferentialGlobalConstantMap k B
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k) cB
include hcoeff
variable [hopen : IsOpenImmersion (Spec.map q)]

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestriction_D (a : A) :
    affineDifferentialGlobalRestriction k A B q hcoeff
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        (X := op ⊤) ((Scheme.ΓSpecIso A).inv a)) =
    (schemeDifferentialSheafDerivation (Spec B) (CommRingCat.of k) cB).d
      (X := op ⊤) ((Scheme.ΓSpecIso B).inv (q a)) := by sorry
