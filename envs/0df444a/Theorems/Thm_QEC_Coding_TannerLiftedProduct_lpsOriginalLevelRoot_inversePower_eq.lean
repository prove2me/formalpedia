-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_inversePower_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:20:49.59713+00:00
-- url     : https://prove2.me/theorems/dfcecc15-286b-4ddb-a512-84e3a251e4a8
-- title:
--   Tanner Lifted Product: lps Original Level Root inverse Power eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Root inverse Power eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L207-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L207-L213

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower_eq (R : Type*) [Field R]
    (N : ℕ) (hN : 0 < N) (ζ : R) (hζ : ζ^N = 1) :
    ζ^(N-1) = ζ⁻¹ := by sorry
