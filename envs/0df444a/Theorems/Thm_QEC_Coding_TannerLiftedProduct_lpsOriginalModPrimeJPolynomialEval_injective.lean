-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:32:15.603348+00:00
-- url     : https://prove2.me/theorems/f99cff1b-766f-4b74-adcd-24535c98c121
-- title:
--   Tanner Lifted Product: lps Original Mod Prime JPolynomial Eval injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Mod Prime JPolynomial Eval injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L24-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L24-L37

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalModPrimeJPolynomialEval p) := by sorry
