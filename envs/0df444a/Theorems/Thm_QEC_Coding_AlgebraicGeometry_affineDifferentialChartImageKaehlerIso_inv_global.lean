-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartImageKaehlerIso_inv_global
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_inv_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:26.319667+00:00
-- url     : https://prove2.me/theorems/17d1aca1-e1ee-43eb-b6b0-79d0125bf07f
-- title:
--   Algebraic Geometry: affine Differential Chart Image Kaehler Iso inv global
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Chart Image Kaehler Iso inv global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L309-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean#L309-L320

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

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_inv_global (s : Γ(OmegaX, ⊤)) :
    (affineDifferentialChartImageKaehlerIso k A f c hf).inv
      ((OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    affineDifferentialGlobalRestrictionToKaehler k X c A f hf s := by sorry
