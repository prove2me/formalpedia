-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_heightOneStalkValuationRingEquiv_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneStalkValuationRingEquiv_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:57.76574+00:00
-- url     : https://prove2.me/theorems/784ea3da-4804-4e35-bf77-58f7381d6af9
-- title:
--   Valuation Centres: height One Stalk Valuation Ring Equiv algebra Map
-- statement:
--   The Valuation Centres construction uses the height One Stalk Valuation Ring Equiv algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L101-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L101-L118

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneStalkValuationRingEquiv_algebraMap
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) (a : R) :
    ((heightOneStalkValuationRingEquiv R H)
      (algebraMap R ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
        (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) a)).val = algebraMap R K a := by sorry
