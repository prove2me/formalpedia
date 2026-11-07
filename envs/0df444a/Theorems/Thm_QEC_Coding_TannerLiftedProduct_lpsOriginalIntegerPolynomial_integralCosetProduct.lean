-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_integralCosetProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_integralCosetProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:12.345834+00:00
-- url     : https://prove2.me/theorems/3d44cf71-5578-458b-bece-621145b918ac
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial integral Coset Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial integral Coset Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L176-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L176-L192

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_integralCosetProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalCosetIntegralCuspSeries N hN x)) := by sorry
