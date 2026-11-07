-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi3_bijective
-- name    : QEC.Coding.f256MFEpi3_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:52.377208+00:00
-- url     : https://prove2.me/theorems/b87c1e89-9445-40d1-905b-5e62fedf77b7
-- title:
--   Coding: f256 MFEpi3 bijective
-- statement:
--   Each actual coordinate permutation is bijective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L130-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L130-L131

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi3_bijective : Function.Bijective f256MFEpi3 := by sorry
