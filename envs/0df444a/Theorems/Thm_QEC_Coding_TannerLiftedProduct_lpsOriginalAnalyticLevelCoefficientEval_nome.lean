-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticLevelCoefficientEval_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticLevelCoefficientEval_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:23:13.519595+00:00
-- url     : https://prove2.me/theorems/6b67d081-5a96-409c-a6e8-963b26cf1bbc
-- title:
--   Tanner Lifted Product: lps Original Analytic Level Coefficient Eval nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Level Coefficient Eval nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L77-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L77-L86

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticLevelCoefficientEval_nome
    (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (lpsOriginalAnalyticCuspLocalizedNomeEval τ).comp
      (lpsOriginalAnalyticLevelCoefficientEval N hN) =
      (Polynomial.evalRingHom (lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ))).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by sorry
