-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_split
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:09.283577+00:00
-- url     : https://prove2.me/theorems/de14f70a-36cf-4bec-a1d9-4a8bece6ac25
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product split
-- statement:
--   Apply genuine CRT twice and normalize the coprime odd cofactor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L39-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L39-L68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_split (q t v L : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (hL : 0<L) (hcL : L.Coprime (2*q)) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^t*q^v*L))) :
    lpsThetaCuspGaussProduct q a (2^t*q^v*L)=
      (L:ℂ)^2*lpsThetaCuspGaussProduct q (a*((q^v*L:ℕ):ℤ)) (2^t)*
        lpsThetaCuspGaussProduct q (a*((2^t*L:ℕ):ℤ)) (q^v) := by sorry
