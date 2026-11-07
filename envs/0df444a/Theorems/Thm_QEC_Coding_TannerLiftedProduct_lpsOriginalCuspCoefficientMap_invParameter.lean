-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_invParameter
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_invParameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:21.854984+00:00
-- url     : https://prove2.me/theorems/9a76703d-3c5e-458b-8158-4a623a9056ce
-- title:
--   Tanner Lifted Product: lps Original Cusp Coefficient Map inv Parameter
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Coefficient Map inv Parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L76-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L76-L90

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_invParameter {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) :
    lpsOriginalCuspCoefficientMap f
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))=
      IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing S)
        (PowerSeries.X : PowerSeries S) := by sorry
