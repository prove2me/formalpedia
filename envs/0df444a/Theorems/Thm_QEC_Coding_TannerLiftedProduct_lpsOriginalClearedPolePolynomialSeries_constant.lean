-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedPolePolynomialSeries_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedPolePolynomialSeries_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:38.100559+00:00
-- url     : https://prove2.me/theorems/2eb804a7-d126-4aa3-8ce9-9f947867bebf
-- title:
--   Tanner Lifted Product: lps Original Cleared Pole Polynomial Series constant
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cleared Pole Polynomial Series constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L244-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L244-L260

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedPolePolynomialSeries_constant {R : Type*} [CommRing R]
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F=1)
    (m : ℕ) (hm : 0<m) (P : Polynomial R) :
    PowerSeries.constantCoeff (lpsOriginalClearedPolePolynomialSeries F m P.natDegree P)=
      P.leadingCoeff := by sorry
