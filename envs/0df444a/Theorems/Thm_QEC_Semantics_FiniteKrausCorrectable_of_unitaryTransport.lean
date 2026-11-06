-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausCorrectable_of_unitaryTransport
-- name    : QEC.Semantics.FiniteKrausCorrectable.of_unitaryTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:12:07.105767+00:00
-- url     : https://prove2.me/theorems/0113fdba-3d29-4f33-ae3f-5ef40fc06ee8
-- title:
--   Finite Kraus Correctable: of unitary Transport
-- statement:
--   The Finite Kraus Correctable construction uses the of unitary Transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L506-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L506-L530

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_Correctable_of_unitaryTransport
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausCorrectable
variable {ι : Type v} [Fintype ι]
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]

theorem QEC.Semantics.FiniteKrausCorrectable.of_unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K}
    {recovery : QuantumChannel Kt Ht}
    (h : FiniteKrausCorrectable ι Ht Kt (C.transport U)
      (noise.unitaryTransport U V) recovery) :
    FiniteKrausCorrectable ι H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by sorry
