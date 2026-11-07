-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_neZero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_neZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:16.556336+00:00
-- url     : https://prove2.me/theorems/67ed13e1-63ae-492f-af4c-2ef2fee0b5f7
-- title:
--   Tanner Lifted Product: lps Original Level Root ne Zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Root ne Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L69-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L69-L74

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_neZero
    (R : Type*) [CommRing R] [Nontrivial R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ ≠ 0 := by sorry
