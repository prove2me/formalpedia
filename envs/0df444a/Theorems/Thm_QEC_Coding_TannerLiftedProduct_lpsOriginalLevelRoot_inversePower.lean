-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_inversePower
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:01.31688+00:00
-- url     : https://prove2.me/theorems/a3b001ae-cd0c-4cbe-8531-096311d9048f
-- title:
--   Tanner Lifted Product: lps Original Level Root inverse Power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Root inverse Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L76-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L76-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower
    (R : Type*) [CommRing R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ * ζ^(N-1) = 1 := by sorry
