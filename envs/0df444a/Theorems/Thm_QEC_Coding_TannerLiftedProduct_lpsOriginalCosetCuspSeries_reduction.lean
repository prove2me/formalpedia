-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspSeries_reduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspSeries_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:20:52.086215+00:00
-- url     : https://prove2.me/theorems/80cc77f1-9a25-4672-8201-e72899d692cd
-- title:
--   Tanner Lifted Product: lps Original Coset Cusp Series reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Cusp Series reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L175-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L175-L182

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspSeries_reduction
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspCoefficientMap
      (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))
      (lpsOriginalCosetIntegralCuspSeries N hN x) =
        lpsOriginalCosetResidueCuspSeries N hN p hp x := by sorry
