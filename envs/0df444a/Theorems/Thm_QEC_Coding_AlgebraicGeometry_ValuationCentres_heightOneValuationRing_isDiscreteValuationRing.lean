-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_heightOneValuationRing_isDiscreteValuationRing
-- name    : QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneValuationRing_isDiscreteValuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:20.571988+00:00
-- url     : https://prove2.me/theorems/db911448-6d11-4f85-ab37-b0d678406984
-- title:
--   Valuation Centres: height One Valuation Ring is Discrete Valuation Ring
-- statement:
--   The Valuation Centres construction uses the height One Valuation Ring is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L120-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L120-L124

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneValuationRing_isDiscreteValuationRing
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) :
    IsDiscreteValuationRing (H.valuationSubringAtPrime K) := by sorry
