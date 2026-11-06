-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionKaehler_eq_map
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:04.427529+00:00
-- url     : https://prove2.me/theorems/4052148e-4fdf-49d7-80a3-6c4a74a9fcfa
-- title:
--   Algebraic Geometry: affine Differential Global Restriction Kaehler eq map
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Restriction Kaehler eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L173-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L173-L177

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
include hq

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalRestrictionKaehler_eq_map (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s =
      KaehlerDifferential.map k k A B s := by sorry
