-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_jWidth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_jWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:09.719609+00:00
-- url     : https://prove2.me/theorems/fe98dfdd-a1e9-428d-9845-ff8a9b2a99b5
-- title:
--   Tanner Lifted Product: lps Original Cusp Coefficient Map j Width
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Coefficient Map j Width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L125-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L125-L132

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_jWidth {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) (hm : m≠0) :
    lpsOriginalCuspCoefficientMap f (lpsOriginalCuspJWidth R m hm)=
      lpsOriginalCuspJWidth S m hm := by sorry
