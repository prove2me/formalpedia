-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehlerLinear_eq
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehlerLinear_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:34.767173+00:00
-- url     : https://prove2.me/theorems/9ded6b2c-c56a-45f2-9e41-cf7a74b62876
-- title:
--   Algebraic Geometry: affine Differential Global Restriction Kaehler Linear eq
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Restriction Kaehler Linear eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L162-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L162-L170

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
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehlerLinear_eq :
    affineDifferentialGlobalRestrictionKaehlerLinear k A B q hcoeff hq =
      KaehlerDifferential.map k k A B := by sorry
