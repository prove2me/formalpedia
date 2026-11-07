-- Prove2me | Theorems.Thm_QEC_Coding_f256MFE_ternary_reverse_mul
-- name    : QEC.Coding.f256MFE_ternary_reverse_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:07.044046+00:00
-- url     : https://prove2.me/theorems/f7764bd2-2e47-4921-b294-3d2a6038f684
-- title:
--   Coding: f256 MFE ternary reverse mul
-- statement:
--   The concrete maps satisfy the degree-three reverse-multiplication identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L134-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L134-L159

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFE_ternary_reverse_mul (x y z : F256) :
    f256MFEPsi (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
      f256MFEpi3Action (f256MFESigma z)) = x * y * z := by sorry
