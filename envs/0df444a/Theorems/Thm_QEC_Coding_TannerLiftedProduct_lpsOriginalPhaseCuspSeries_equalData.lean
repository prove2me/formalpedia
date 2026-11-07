-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_equalData
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_equalData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:18:36.41228+00:00
-- url     : https://prove2.me/theorems/38f52dc2-5a72-4230-af23-f9b8a2436a99
-- title:
--   Tanner Lifted Product: lps Original Phase Cusp Series equal Data
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Phase Cusp Series equal Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L101-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L101-L130

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_equalData
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hζ : ζ^N = 1) (hη : η^N = 1)
    (he : lpsOriginalPhaseCuspSeries R N m hm ζ =
      lpsOriginalPhaseCuspSeries R N n hn η) : m = n ∧ ζ = η := by sorry
