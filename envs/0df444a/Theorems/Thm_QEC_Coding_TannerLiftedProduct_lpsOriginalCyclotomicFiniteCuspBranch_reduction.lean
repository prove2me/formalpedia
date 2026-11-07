-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFiniteCuspBranch_reduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:06.910972+00:00
-- url     : https://prove2.me/theorems/4b5ca631-74a3-4727-b7c3-d363719fc1a1
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Finite Cusp Branch reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Finite Cusp Branch reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L145-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L145-L158

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_reduction (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicCuspReduction p (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalCuspJWidth (ZMod p) 1 (by decide) := by sorry
