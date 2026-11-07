-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFEpsi_surjective
-- name    : QEC.Coding.f256RMFEpsi_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:19.54483+00:00
-- url     : https://prove2.me/theorems/086d03bf-d72c-490b-84cb-53f0bf61c0b9
-- title:
--   Coding: f256 RMFEpsi surjective
-- statement:
--   The concrete weighted trace projection reaches both binary values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L55-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L55-L57

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFEpsi_surjective : Function.Surjective f256RMFEpsi := by sorry
