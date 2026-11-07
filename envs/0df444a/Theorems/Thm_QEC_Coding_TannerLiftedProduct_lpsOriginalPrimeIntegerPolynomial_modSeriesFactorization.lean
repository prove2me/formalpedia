-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:33:55.356198+00:00
-- url     : https://prove2.me/theorems/285be179-09d4-44d1-9722-0a303448422a
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial mod Series Factorization
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial mod Series Factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L204-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L204-L215

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalModPrimeCoefficientEval p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by sorry
