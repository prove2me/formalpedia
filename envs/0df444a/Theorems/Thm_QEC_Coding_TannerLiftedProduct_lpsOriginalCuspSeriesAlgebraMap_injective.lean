-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeriesAlgebraMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:46.708862+00:00
-- url     : https://prove2.me/theorems/70930548-6c68-4d0d-915e-84d51d2616e1
-- title:
--   Tanner Lifted Product: lps Original Cusp Series Algebra Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Series Algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L171-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L171-L176

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeriesAlgebraMap_injective (R : Type*) [CommRing R] [IsDomain R] :
    Function.Injective (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)) := by sorry
