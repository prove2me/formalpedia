-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_coprime_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_coprime_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:23.416477+00:00
-- url     : https://prove2.me/theorems/f13b06df-a801-4d4b-b751-13a496aca850
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product coprime mul
-- statement:
--   The genuine Gauss CRT formula factors the four-variable cusp product at coprime moduli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L76-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_coprime_mul (q m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ℤ) :
    lpsThetaCuspGaussProduct q a (m*n)=
      lpsThetaCuspGaussProduct q (a*(n:ℤ)) m *
        lpsThetaCuspGaussProduct q (a*(m:ℤ)) n := by sorry
