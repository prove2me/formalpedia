-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_four
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:49.285199+00:00
-- url     : https://prove2.me/theorems/d6ddc6ec-d72d-4072-b9de-d4399a3662c9
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product four
-- statement:
--   Inflation computes the three scaled Gauss factors at modulus four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L136-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L136-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_four (q : ℕ) (a : ℤ) :
    lpsThetaCuspGaussProduct q a 4=64*lpsUnaryQuadraticGauss a 4 := by sorry
