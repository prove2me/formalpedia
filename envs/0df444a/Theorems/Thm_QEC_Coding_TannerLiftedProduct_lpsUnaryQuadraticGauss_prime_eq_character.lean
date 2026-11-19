-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_prime_eq_character
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_eq_character
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:14.708407+00:00
-- url     : https://prove2.me/theorems/8fd6a1f6-c93a-496e-b973-7a57d28bbcda
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss prime eq character
-- statement:
--   The finite-field quadratic Gauss sum is the actual quadratic character times the standard Gauss sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L32-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L32-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_eq_character (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : ℤ) (ha : (a:ZMod q)≠0) :
    lpsUnaryQuadraticGauss a q=lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by sorry
