-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetResiduePhase_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResiduePhase_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:18:21.237166+00:00
-- url     : https://prove2.me/theorems/44661f9e-1113-4304-bef5-14b3318ae885
-- title:
--   Tanner Lifted Product: lps Original Coset Residue Phase pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Residue Phase pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L184-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L184-L189

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResiduePhase_pow
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))^N = 1 := by sorry
