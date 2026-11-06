-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehler_D
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:30.990204+00:00
-- url     : https://prove2.me/theorems/95e73dda-69bc-4460-87fd-8d812e931b6b
-- title:
--   Algebraic Geometry: affine Differential Global Restriction Kaehler D
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Restriction Kaehler D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L109-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L109-L124

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

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_D (a : A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k B (q a) := by sorry
