-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetClearedCusp_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetClearedCusp_pullback
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:43:03.02507+00:00
-- url     : https://prove2.me/theorems/0649ba41-30fa-4161-91ac-4ae9afae55e9
-- title:
--   Tanner Lifted Product: lps Original Coset Cleared Cusp pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Cleared Cusp pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L262-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L262-L273

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetClearedCusp_pullback
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (σ : ℍ) :
    lpsOriginalClearedAffineCusp (N^2)
      (lpsOriginalCosetCuspWitness N hN x).1.val
      (lpsOriginalCosetCuspWitness N hN x).2.val
      (Function.Periodic.qParam 1 (σ : ℂ)) =
      Function.Periodic.qParam 1 (σ : ℂ)^(N^2) *
        lpsOriginalJDilated N hN
          (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • σ)) := by sorry
