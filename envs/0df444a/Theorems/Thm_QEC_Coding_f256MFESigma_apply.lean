-- Prove2me | Theorems.Thm_QEC_Coding_f256MFESigma_apply
-- name    : QEC.Coding.f256MFESigma_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:19.402784+00:00
-- url     : https://prove2.me/theorems/4618e6fe-27b7-441e-a5f1-7bb548f9722c
-- title:
--   Coding: f256 MFESigma apply
-- statement:
--   Evaluation of the concrete coordinate embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L87-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L87-L89

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFESigma_apply (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by sorry
