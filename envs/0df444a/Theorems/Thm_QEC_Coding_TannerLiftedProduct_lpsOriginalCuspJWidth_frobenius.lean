-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspJWidth_frobenius
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJWidth_frobenius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:03.855543+00:00
-- url     : https://prove2.me/theorems/5645439d-87bb-4fa7-afc9-7929704d62ea
-- title:
--   Tanner Lifted Product: lps Original Cusp JWidth frobenius
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp JWidth frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L160-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L160-L169

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJWidth_frobenius (R : Type*) [CommRing R]
    (p : ℕ) [ExpChar R p] (hp : p≠0) (m : ℕ) (hm : m≠0) :
    (lpsOriginalCuspJWidth R m hm)^p=
      lpsOriginalCuspJWidth R (m*p) (Nat.mul_ne_zero hm hp) := by sorry
