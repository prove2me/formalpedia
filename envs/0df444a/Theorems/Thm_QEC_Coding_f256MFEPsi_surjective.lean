-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEPsi_surjective
-- name    : QEC.Coding.f256MFEPsi_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:58.060224+00:00
-- url     : https://prove2.me/theorems/84a20b36-6c78-4be2-bef4-e6c1e3de32aa
-- title:
--   Coding: f256 MFEPsi surjective
-- statement:
--   The contraction map has a concrete preimage for every field element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L162-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L162-L166

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEPsi_surjective : Function.Surjective f256MFEPsi := by sorry
