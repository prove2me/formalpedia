-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_shifted_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_shifted_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:19:08.256274+00:00
-- url     : https://prove2.me/theorems/a561f142-ecd9-4a15-bb7e-4eabc5ed64ba
-- title:
--   Tanner Lifted Product: lps Original Phase Cusp Numerator shifted taylor
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Phase Cusp Numerator shifted taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L234-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L234-L244

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_shifted_taylor
    (N : ℕ) (hN : 0 < N) (B m : ℕ) (hm : m ≠ 0) (r : ℚ)
    (hr : ∃ z : ℤ, (N : ℚ) * r = z) :
    PowerSeries.X^(B-m) * lpsOriginalPhaseCuspNumerator ℂ N m hm
      (Function.Periodic.qParam 1 (r : ℂ)) =
        lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B m r) := by sorry
