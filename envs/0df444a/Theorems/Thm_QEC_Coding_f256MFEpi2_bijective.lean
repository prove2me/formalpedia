-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEpi2_bijective
-- name    : QEC.Coding.f256MFEpi2_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:51.460714+00:00
-- url     : https://prove2.me/theorems/234233db-ed16-4a00-9fe6-59b8ab9a2ed6
-- title:
--   Coding: f256 MFEpi2 bijective
-- statement:
--   Each actual coordinate permutation is bijective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L126-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L126-L127

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEpi2_bijective : Function.Bijective f256MFEpi2 := by sorry
