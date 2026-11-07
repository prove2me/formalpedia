-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicSeries_rescaleReduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicSeries_rescaleReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:01.683122+00:00
-- url     : https://prove2.me/theorems/2a6d2871-5cb5-4ba1-a29a-b49937d96e7a
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Series rescale Reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Series rescale Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L97-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L97-L107

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicSeries_rescaleReduction (p : ℕ) [Fact p.Prime]
    (m : ℕ) :
    PowerSeries.map (lpsOriginalCyclotomicReduction p)
      (PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
        (PowerSeries.map (algebraMap ℤ (lpsOriginalCyclotomicCoefficientRing p))
          lpsOriginalJZSeries))=
      PowerSeries.map (Int.castRingHom (ZMod p)) lpsOriginalJZSeries := by sorry
