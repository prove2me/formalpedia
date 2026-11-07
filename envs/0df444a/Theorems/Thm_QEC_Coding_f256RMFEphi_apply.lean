-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFEphi_apply
-- name    : QEC.Coding.f256RMFEphi_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:13.157224+00:00
-- url     : https://prove2.me/theorems/0afd2d5e-790a-4fd8-8890-a50b60bf299d
-- title:
--   Coding: f256 RMFEphi apply
-- statement:
--   The linear embedding evaluates to the concrete algebra map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L14-L16
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L14-L16

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFEphi_apply (bit : ZMod 2) :
    f256RMFEphi bit = algebraMap (ZMod 2) F256 bit := by sorry
