-- Prove2me | Theorems.Thm_QEC_Locality_unitaryTransport_toQuantumChannel
-- name    : QEC.Locality.unitaryTransport_toQuantumChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:58.673395+00:00
-- url     : https://prove2.me/theorems/ba33e130-2a45-4b91-aeff-449b9c981b31
-- title:
--   Locality: unitary Transport to Quantum Channel
-- statement:
--   The Locality construction uses the unitary Transport to Quantum Channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L932-L952
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L932-L952

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.unitaryTransport_toQuantumChannel {κ : Type v} [Fintype κ]
    {H K Ht Kt : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht]
    [FiniteQuantumSystem Ht] [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt]
    [FiniteQuantumSystem Kt] (E : FiniteKrausFamily κ H K)
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (hE : E.Complete) :
    (E.unitaryTransport U V).toQuantumChannel
        (E.unitaryTransport_complete U V hE) =
      QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp (E.toQuantumChannel hE)
          (QuantumChannel.unitaryConj U.symm)) := by sorry
