-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSeriesFrobenius
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerSeriesFrobenius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:51.212923+00:00
-- url     : https://prove2.me/theorems/71267107-d1da-47fd-972c-b9843032b9ba
-- title:
--   Tanner Lifted Product: lps Original Integer Series Frobenius
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Series Frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L20-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L20-L38

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerSeriesFrobenius
    (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p] (hp : p≠0)
    (F : PowerSeries ℤ) :
    (PowerSeries.map (Int.castRingHom R) F)^p=
      PowerSeries.expand p hp (PowerSeries.map (Int.castRingHom R) F) := by sorry
