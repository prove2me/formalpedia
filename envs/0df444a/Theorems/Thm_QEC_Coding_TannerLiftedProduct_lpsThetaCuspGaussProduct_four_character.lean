-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_four_character
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_four_character
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:53.657244+00:00
-- url     : https://prove2.me/theorems/b5a2cfb4-af79-42e4-bcf2-5806ed902923
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product four character
-- statement:
--   The modulus-four theta product is expressed through the actual additive phase and character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L199-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L199-L205

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_four_character (q : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod 4)) :
    lpsThetaCuspGaussProduct q a 4=16*(8+4*
      gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character (a:ZMod 4)) := by sorry
