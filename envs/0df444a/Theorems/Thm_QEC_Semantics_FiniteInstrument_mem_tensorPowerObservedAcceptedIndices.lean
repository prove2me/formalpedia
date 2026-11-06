-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
-- name    : QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:43:37.955714+00:00
-- url     : https://prove2.me/theorems/14c82037-a39e-49dd-84a4-656cd0d628c0
-- title:
--   Finite Instrument: mem tensor Power Observed Accepted Indices
-- statement:
--   The Finite Instrument construction uses the mem tensor Power Observed Accepted Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L105-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean#L105-L114

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (rawHistory : tensorPowerHistory κ attempts) (trial : Fin attempts) :
    trial ∈ tensorPowerObservedAcceptedIndices I accepts attempts rawHistory ↔
      accepts (tensorPowerObservedHistoryAt I attempts rawHistory trial) := by sorry
