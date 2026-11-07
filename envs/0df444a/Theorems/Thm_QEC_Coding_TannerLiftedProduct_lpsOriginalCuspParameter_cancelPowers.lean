-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspParameter_cancelPowers
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspParameter_cancelPowers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:31.38122+00:00
-- url     : https://prove2.me/theorems/fcc11979-2e47-43de-b636-e9cf73d17236
-- title:
--   Tanner Lifted Product: lps Original Cusp Parameter cancel Powers
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Parameter cancel Powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L262-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L262-L270

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspParameter_cancelPowers {R : Type*} [CommRing R]
    (m D i : ℕ) (hi : i≤D) :
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*D) *
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^(m*i)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*(D-i)) := by sorry
