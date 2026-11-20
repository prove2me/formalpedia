-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__frobenius_e48cc4f8f4fd
-- name    : P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__frobenius_e48cc4f8f4fd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:58:26.468923+00:00
-- url     : https://prove2.me/theorems/8b521b76-14a5-4705-8907-5d4535a8d52c
-- title:
--   P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  frobenius e48cc4f8f4fd: P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  frobenius e48cc4f8f4fd
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  frobenius e48cc4f8f4fd construction uses the P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  frobenius e48cc4f8f4fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L23-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L23-L28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__frobenius_e48cc4f8f4fd
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Polynomial ℤ) (x : K) :
    (P.eval₂ (Int.castRingHom K) x)^p = P.eval₂ (Int.castRingHom K) (x^p) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«lpsOriginalIntegerPolynomial_eval₂_frobenius» := P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__frobenius_e48cc4f8f4fd
