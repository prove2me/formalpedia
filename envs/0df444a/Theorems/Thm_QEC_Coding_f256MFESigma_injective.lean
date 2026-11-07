-- Prove2me | Theorems.Thm_QEC_Coding_f256MFESigma_injective
-- name    : QEC.Coding.f256MFESigma_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:31.6902+00:00
-- url     : https://prove2.me/theorems/a7561b97-70f2-4b05-a657-d52e18e0f87f
-- title:
--   Coding: f256 MFESigma injective
-- statement:
--   The concrete coordinate embedding is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L118-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L118-L123

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFESigma_injective : Function.Injective f256MFESigma := by sorry
