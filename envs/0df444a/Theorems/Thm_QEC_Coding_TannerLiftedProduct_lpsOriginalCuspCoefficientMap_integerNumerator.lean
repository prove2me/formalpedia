-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_integerNumerator
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_integerNumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:57.517193+00:00
-- url     : https://prove2.me/theorems/bf00ec56-f6e7-473b-aa3f-06fccc35cc94
-- title:
--   Tanner Lifted Product: lps Original Cusp Coefficient Map integer Numerator
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Coefficient Map integer Numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L119-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L119-L123

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_integerNumerator {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (lpsOriginalCuspJNumerator R)=lpsOriginalCuspJNumerator S := by sorry
