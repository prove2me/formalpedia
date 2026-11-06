-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_le_heightOne
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_le_heightOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:22.938992+00:00
-- url     : https://prove2.me/theorems/25667d9a-c90f-4fa0-8efc-47dd9cb557d8
-- title:
--   Algebraic Geometry: kaehler field map range le height One
-- statement:
--   An actual affine differential preimage maps into the same-field valuation ring at its genuine height-one centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L152-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L152-L175

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_le_heightOne
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R A K).range) :
    omega ∈ (KaehlerDifferential.map R R T K).range := by sorry
