-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:42.96649+00:00
-- url     : https://prove2.me/theorems/835cd1b6-ff0b-44af-b2ec-ef322b870bba
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product two
-- statement:
--   A unit first column at modulus two makes the actual theta Gauss product zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L130-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L130-L133

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two (q : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod 2)) :
    lpsThetaCuspGaussProduct q a 2=0 := by sorry
