-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFEpsi_phi
-- name    : QEC.Coding.f256RMFEpsi_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:18.395021+00:00
-- url     : https://prove2.me/theorems/91eccc74-8c6b-49bf-acae-392b8c725c57
-- title:
--   Coding: f256 RMFEpsi phi
-- statement:
--   The weighted trace projection is a left inverse to the concrete embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L44-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L44-L52

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFEpsi_phi (bit : ZMod 2) :
    f256RMFEpsi (f256RMFEphi bit) = bit := by sorry
