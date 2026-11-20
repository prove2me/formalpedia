-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
-- name    : P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:58:24.256921+00:00
-- url     : https://prove2.me/theorems/f4f18d28-92a5-4bc7-94ea-693debdccdbe
-- title:
--   P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  hom 5c9005d9bf86: P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  hom 5c9005d9bf86
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  hom 5c9005d9bf86 construction uses the P2 M QEC Coding Tanner Lifted Product lps Original Integer Polynomial eval  hom 5c9005d9bf86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L13-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L13-L21

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : Polynomial ℤ) (x : R) :
    f (P.eval₂ (Int.castRingHom R) x) = P.eval₂ (Int.castRingHom S) (f x) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«lpsOriginalIntegerPolynomial_eval₂_hom» := P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
