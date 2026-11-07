-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi2_apply
-- name    : QEC.Coding.f256MFEpi2_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:52.532393+00:00
-- url     : https://prove2.me/theorems/ad4fa62c-0452-4618-aeff-426c877000c7
-- title:
--   Coding: f256 MFEpi2 apply
-- statement:
--   The first permutation sends `(i,j,k)` to `(j,k,i)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L77-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L77-L79

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi2_apply (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by sorry
