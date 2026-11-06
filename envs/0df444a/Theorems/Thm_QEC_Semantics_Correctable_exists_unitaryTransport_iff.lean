-- Prove2me | Theorems.Thm_QEC_Semantics_Correctable_exists_unitaryTransport_iff
-- name    : QEC.Semantics.Correctable.exists_unitaryTransport_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:48:48.377201+00:00
-- url     : https://prove2.me/theorems/35fd0775-1759-4ecb-890b-b9f06d2f8277
-- title:
--   Correctable: exists unitary Transport iff
-- statement:
--   The Correctable construction uses the exists unitary Transport iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L287-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L287-L304

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

theorem QEC.Semantics.Correctable.exists_unitaryTransport_iff
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      Correctable Ht Kt (C.transport U)
        (QuantumChannel.comp (QuantumChannel.unitaryConj V)
          (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
        recovery) ↔
    (∃ recovery : QuantumChannel K H, Correctable H K C noise recovery) := by sorry
