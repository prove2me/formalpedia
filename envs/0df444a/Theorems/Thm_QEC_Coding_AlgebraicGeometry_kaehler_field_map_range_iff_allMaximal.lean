-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_iff_allMaximal
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff_allMaximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:25.392203+00:00
-- url     : https://prove2.me/theorems/9e7ef8c1-c7b1-40ee-bfcb-99f317eb1693
-- title:
--   Algebraic Geometry: kaehler field map range iff all Maximal
-- statement:
--   The actual affine differential image equals membership in the actual images from every maximal localization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L82-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L82-L96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K]
variable (B : ∀ (P : Ideal A) [P.IsMaximal], Type*)
variable [∀ (P : Ideal A) [P.IsMaximal], CommRing (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (B P) P]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra R (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R (B P) K]

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff_allMaximal
    (omega : KaehlerDifferential R K) :
    omega ∈ (KaehlerDifferential.map R R A K).range ↔
      ∀ (P : Ideal A) [P.IsMaximal], omega ∈ (KaehlerDifferential.map R R (B P) K).range := by sorry
