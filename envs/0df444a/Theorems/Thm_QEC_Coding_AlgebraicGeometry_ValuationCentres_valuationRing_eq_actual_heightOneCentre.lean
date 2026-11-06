-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_valuationRing_eq_actual_heightOneCentre
-- name    : QEC.Coding.AlgebraicGeometry.ValuationCentres.valuationRing_eq_actual_heightOneCentre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:55.327746+00:00
-- url     : https://prove2.me/theorems/d5a4755a-de02-4772-b2cd-ec4062ec8198
-- title:
--   Valuation Centres: valuation Ring eq actual height One Centre
-- statement:
--   A genuine nontrivial valuation dominating a Dedekind model has the same
--   valuation ring as the model's height-one localization at its actual centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L48-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L48-L86

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.ValuationCentres.valuationRing_eq_actual_heightOneCentre
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hn : ∃ r : R, r ≠ 0 ∧ v (algebraMap R K r) < 1) :
    ∃ H : IsDedekindDomain.HeightOneSpectrum R,
      H.asIdeal = Ideal.comap ((algebraMap R K).codRestrict v.valuationSubring hR)
        (IsLocalRing.maximalIdeal v.valuationSubring) ∧
      H.valuationSubringAtPrime K = v.valuationSubring := by sorry
