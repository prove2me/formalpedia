-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFEpsi_apply
-- name    : QEC.Coding.f256RMFEpsi_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:42.110548+00:00
-- url     : https://prove2.me/theorems/9af6a4f5-3202-49f7-b8e4-ce65e49f5c55
-- title:
--   Coding: f256 RMFEpsi apply
-- statement:
--   The linear projection evaluates to the concrete weighted trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L19-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L19-L21

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFEpsi_apply (x : F256) :
    f256RMFEpsi x = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3 * x) := by sorry
