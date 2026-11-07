-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi2_sigma_apply
-- name    : QEC.Coding.f256MFEpi2_sigma_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:22.008468+00:00
-- url     : https://prove2.me/theorems/b0b03ad2-6e8c-486b-b424-ded31b07341c
-- title:
--   Coding: f256 MFEpi2 sigma apply
-- statement:
--   The first action exposes the second polynomial coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L104-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L104-L108

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi2_sigma_apply (y : F256) (i j k : Fin 8) :
    f256MFEpi2Action (f256MFESigma y) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun y j := by sorry
