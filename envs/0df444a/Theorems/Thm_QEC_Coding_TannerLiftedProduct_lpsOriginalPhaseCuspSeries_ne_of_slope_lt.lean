-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_ne_of_slope_lt
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_ne_of_slope_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:17:44.661689+00:00
-- url     : https://prove2.me/theorems/7e23343e-c449-48b7-b917-fd22591d7cba
-- title:
--   Tanner Lifted Product: lps Original Phase Cusp Series ne of slope lt
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Phase Cusp Series ne of slope lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L82-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L82-L99

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_ne_of_slope_lt
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hη : η^N = 1) (hmn : m < n) :
    lpsOriginalPhaseCuspSeries R N m hm ζ ≠
      lpsOriginalPhaseCuspSeries R N n hn η := by sorry
