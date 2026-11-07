-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFE_ternary_reverse_mul
-- name    : QEC.Coding.f256RMFE_ternary_reverse_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:20.317899+00:00
-- url     : https://prove2.me/theorems/ced21f6b-48b9-497d-aa55-fc4f6aefd56b
-- title:
--   Coding: f256 RMFE ternary reverse mul
-- statement:
--   The concrete maps satisfy the degree-three reverse-multiplication identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L60-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L60-L68

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFE_ternary_reverse_mul (x y z : ZMod 2) :
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) = x * y * z := by sorry
