-- Prove2me | Theorems.Thm_QEC_Coding_f256RMFEphi_injective
-- name    : QEC.Coding.f256RMFEphi_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:15.816449+00:00
-- url     : https://prove2.me/theorems/87663a59-d835-4d6c-90dc-5067fdd6f7eb
-- title:
--   Coding: f256 RMFEphi injective
-- statement:
--   The concrete width-one embedding is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean#L38-L41

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256RMFEphi_injective : Function.Injective f256RMFEphi := by sorry
