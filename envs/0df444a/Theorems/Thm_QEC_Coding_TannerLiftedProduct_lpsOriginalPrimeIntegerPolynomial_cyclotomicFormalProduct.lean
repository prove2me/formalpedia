-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:32:37.301201+00:00
-- url     : https://prove2.me/theorems/9f8cf3bd-336b-43b6-8098-f7b1ee41e5df
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial cyclotomic Formal Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial cyclotomic Formal Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L174-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L174-L184

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
      lpsOriginalCyclotomicFormalPrimeProduct p := by sorry
