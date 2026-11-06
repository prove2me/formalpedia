-- Prove2me | Theorems.Thm_QEC_Semantics_Correctable_of_unitaryTransport
-- name    : QEC.Semantics.Correctable.of_unitaryTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:48:22.788199+00:00
-- url     : https://prove2.me/theorems/b3d87a6f-79fd-4a8a-aecd-4d37fbe0dd9c
-- title:
--   Correctable: of unitary Transport
-- statement:
--   The Correctable construction uses the of unitary Transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L263-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L263-L285

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.Correctable
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]

theorem QEC.Semantics.Correctable.of_unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K}
    {recovery : QuantumChannel Kt Ht}
    (h : Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      recovery) :
    Correctable H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by sorry
