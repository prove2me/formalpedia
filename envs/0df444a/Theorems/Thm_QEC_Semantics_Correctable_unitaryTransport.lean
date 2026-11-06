-- Prove2me | Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
-- name    : QEC.Semantics.Correctable.unitaryTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:47:30.764041+00:00
-- url     : https://prove2.me/theorems/5be4cf3b-7ac8-44a6-8aa6-3fc6333df1b8
-- title:
--   Correctable: unitary Transport
-- statement:
--   The Correctable construction uses the unitary Transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L237-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L237-L261

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

theorem QEC.Semantics.Correctable.unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K}
    {recovery : QuantumChannel K H}
    (h : Correctable H K C noise recovery) :
    Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      (QuantumChannel.comp (QuantumChannel.unitaryConj U)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm))) := by sorry
