-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartImageKaehlerIso_restrict
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:29.612964+00:00
-- url     : https://prove2.me/theorems/4e02f0d6-158c-4a59-86d7-372ca637eb4a
-- title:
--   Algebraic Geometry: affine Differential Chart Image Kaehler Iso restrict
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Chart Image Kaehler Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L220-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L220-L243

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
variable {X : Scheme.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k B)
include hq

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_restrict (s : KaehlerDifferential k A) :
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image (Spec.map q) f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : Spec.map q ''ᵁ ⊤ ⟶ ⊤)).op
          ((affineDifferentialChartImageKaehlerIso k A f c hf).hom s)) =
    (schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k B)
      (schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
        (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
        hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)) ⊤).hom
          ((affineDifferentialGlobalSectionsEquiv k B).symm
            (KaehlerDifferential.map k k A B s)) := by sorry
