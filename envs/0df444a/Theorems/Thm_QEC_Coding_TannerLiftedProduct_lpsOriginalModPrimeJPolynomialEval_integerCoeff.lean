-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_integerCoeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_integerCoeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:33:56.373773+00:00
-- url     : https://prove2.me/theorems/0d9e1c15-ea82-45f5-b5a4-f7b435d21dbc
-- title:
--   Tanner Lifted Product: lps Original Mod Prime JPolynomial Eval integer Coeff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Mod Prime JPolynomial Eval integer Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L39-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L39-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_integerCoeff (p : ℕ) [Fact p.Prime] :
    (lpsOriginalModPrimeJPolynomialEval p).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))=
      lpsOriginalModPrimeCoefficientEval p := by sorry
