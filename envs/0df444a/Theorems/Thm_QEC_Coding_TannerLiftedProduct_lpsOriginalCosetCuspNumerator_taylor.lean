-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspNumerator_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspNumerator_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:42:48.382197+00:00
-- url     : https://prove2.me/theorems/114f3d2f-535d-4023-93a9-af90b093b409
-- title:
--   Tanner Lifted Product: lps Original Coset Cusp Numerator taylor
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Cusp Numerator taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L246-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L246-L260

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspNumerator_taylor
    (N : ℕ) (hN : 0 < N) (B : ℕ) (x : LPSOriginalCuspIndex N) :
    PowerSeries.map (lpsOriginalLevelPhaseRing N).val
      (PowerSeries.X^(B-(lpsOriginalCosetCuspData N hN x).1) *
        lpsOriginalPhaseCuspNumerator (lpsOriginalLevelPhaseRing N) N
          (lpsOriginalCosetCuspData N hN x).1
          (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
          (lpsOriginalCosetPhaseElement N hN x)) =
      lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B
        (lpsOriginalCosetCuspWitness N hN x).1.val
        (lpsOriginalCosetCuspWitness N hN x).2.val) := by sorry
