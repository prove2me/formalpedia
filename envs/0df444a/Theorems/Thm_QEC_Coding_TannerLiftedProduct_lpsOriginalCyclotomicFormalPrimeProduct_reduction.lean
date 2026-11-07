-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFormalPrimeProduct_reduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:25:11.925288+00:00
-- url     : https://prove2.me/theorems/5f7057d6-1bc6-4249-91e3-7b2fd4973a55
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Formal Prime Product reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Formal Prime Product reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L192-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L192-L223

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_reduction (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map (lpsOriginalCyclotomicCuspReduction p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by sorry
