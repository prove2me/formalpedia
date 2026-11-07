-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:20.453206+00:00
-- url     : https://prove2.me/theorems/f63cf9f9-6f64-4d32-8daa-73a3033710f9
-- title:
--   Tanner Lifted Product: lps Original Cusp Coefficient Map series
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Coefficient Map series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L69-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L69-L74

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_series {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    lpsOriginalCuspCoefficientMap f
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=
      algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S) (PowerSeries.map f F) := by sorry
