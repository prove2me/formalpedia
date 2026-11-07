-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCosetBranch_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCosetBranch_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:24:01.069461+00:00
-- url     : https://prove2.me/theorems/fc9d6e42-5155-425c-91fb-32dba9d0ff28
-- title:
--   Tanner Lifted Product: lps Original Analytic Coset Branch nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Coset Branch nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L65-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L65-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCosetBranch_nome
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCosetBranch N hN x) =
      lpsOriginalJDilated N hN (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • τ)) := by sorry
