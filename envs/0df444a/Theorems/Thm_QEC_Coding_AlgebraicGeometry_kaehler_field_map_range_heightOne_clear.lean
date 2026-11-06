-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_heightOne_clear
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_heightOne_clear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:24.475903+00:00
-- url     : https://prove2.me/theorems/ef142c8f-b360-4133-a11b-bce5dc7d66a8
-- title:
--   Algebraic Geometry: kaehler field map range height One clear
-- statement:
--   Transport canonical height-one localization to the same actual valuation ring and clear a genuine differential denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L124-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L124-L149

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

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_heightOne_clear
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R T K).range) :
    ∃ s : A, s ∉ H.asIdeal ∧ s • omega ∈ (KaehlerDifferential.map R R A K).range := by sorry
