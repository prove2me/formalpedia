-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausCorrectable_exists_unitaryTransport_iff
-- name    : QEC.Semantics.FiniteKrausCorrectable.exists_unitaryTransport_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:35:34.269817+00:00
-- url     : https://prove2.me/theorems/36de3e06-92e2-48f3-9e89-b7d611133549
-- title:
--   Finite Kraus Correctable: exists unitary Transport iff
-- statement:
--   The Finite Kraus Correctable construction uses the exists unitary Transport iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L532-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L532-L548

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_Correctable_exists_unitaryTransport_iff
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

theorem QEC.Semantics.FiniteKrausCorrectable.exists_unitaryTransport_iff
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      FiniteKrausCorrectable ι Ht Kt (C.transport U)
        (noise.unitaryTransport U V) recovery) ↔
    (∃ recovery : QuantumChannel K H,
      FiniteKrausCorrectable ι H K C noise recovery) := by sorry
