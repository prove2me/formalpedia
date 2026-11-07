-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeries_charP
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeries_charP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:24.760089+00:00
-- url     : https://prove2.me/theorems/a16deb35-d613-4f38-8fe9-35fffe58c1af
-- title:
--   Tanner Lifted Product: lps Original Cusp Series char P
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Series char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L178-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L178-L182

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeries_charP (p : ℕ) [Fact p.Prime] :
    CharP (lpsOriginalCuspSeriesRing (ZMod p)) p := by sorry
