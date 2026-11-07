-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJZSeries_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:36.451728+00:00
-- url     : https://prove2.me/theorems/33dd1b04-ae75-490d-bbb8-8d60faf7bb1c
-- title:
--   Tanner Lifted Product: lps Original JZSeries constant
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JZSeries constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L40-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L40-L48

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJZSeries_constant : PowerSeries.constantCoeff lpsOriginalJZSeries=1 := by sorry
