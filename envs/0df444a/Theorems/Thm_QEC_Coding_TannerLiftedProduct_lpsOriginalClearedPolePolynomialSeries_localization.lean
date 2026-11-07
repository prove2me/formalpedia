-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedPolePolynomialSeries_localization
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedPolePolynomialSeries_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:42.488197+00:00
-- url     : https://prove2.me/theorems/7225de6d-434a-4927-b78f-6ed12f2d628c
-- title:
--   Tanner Lifted Product: lps Original Cleared Pole Polynomial Series localization
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cleared Pole Polynomial Series localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L272-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L272-L298

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedPolePolynomialSeries_localization {R : Type*} [CommRing R]
    (F : PowerSeries R) (m : ℕ) (P : Polynomial R) :
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (lpsOriginalClearedPolePolynomialSeries F m P.natDegree P)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*P.natDegree) *
        P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
          ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
              (PowerSeries.X : PowerSeries R))^m *
            algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F) := by sorry
