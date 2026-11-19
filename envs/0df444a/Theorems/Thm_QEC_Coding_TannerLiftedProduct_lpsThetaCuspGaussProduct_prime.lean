-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:42.031241+00:00
-- url     : https://prove2.me/theorems/bf78eda7-0372-43eb-9ce5-8ad7e771bb1e
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product prime
-- statement:
--   At the residue prime the actual theta Gauss product retains its quadratic character factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L102-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L102-L111

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : ℤ) (ha : (a:ZMod q)≠0) :
    lpsThetaCuspGaussProduct q a q=(q:ℂ)^3*lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by sorry
