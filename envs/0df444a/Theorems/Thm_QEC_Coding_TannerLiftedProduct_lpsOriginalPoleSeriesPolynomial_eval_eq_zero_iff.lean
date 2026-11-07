-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:25.12929+00:00
-- url     : https://prove2.me/theorems/e3b5670f-536d-49b0-a8bd-7d391d586e2a
-- title:
--   Tanner Lifted Product: lps Original Pole Series Polynomial eval eq zero iff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Pole Series Polynomial eval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L300-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L300-L318

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff {R : Type*}
    [CommRing R] [IsDomain R] (F : PowerSeries R)
    (hF : PowerSeries.constantCoeff F=1) (m : ℕ) (hm : 0<m) (P : Polynomial R) :
    P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
      ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^m *
          algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=0 ↔ P=0 := by sorry
