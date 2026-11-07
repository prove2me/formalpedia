-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi3_apply
-- name    : QEC.Coding.f256MFEpi3_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:15.958323+00:00
-- url     : https://prove2.me/theorems/b804e5fe-cc19-4e94-8130-276532ba5154
-- title:
--   Coding: f256 MFEpi3 apply
-- statement:
--   The second permutation sends `(i,j,k)` to `(k,i,j)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L82-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L82-L84

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi3_apply (i j k : Fin 8) :
    f256MFEpi3 (f256MFEIndex i j k) = f256MFEIndex k i j := by sorry
