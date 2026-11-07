-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi3_sigma_apply
-- name    : QEC.Coding.f256MFEpi3_sigma_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:31.553509+00:00
-- url     : https://prove2.me/theorems/16dea3a7-265d-4572-81b0-565ba2cbbeec
-- title:
--   Coding: f256 MFEpi3 sigma apply
-- statement:
--   The second action exposes the third polynomial coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L111-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L111-L115

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi3_sigma_apply (z : F256) (i j k : Fin 8) :
    f256MFEpi3Action (f256MFESigma z) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun z k := by sorry
