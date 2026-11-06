-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_of_unitaryTransport_complete
-- name    : QEC.Semantics.FiniteKrausFamily.of_unitaryTransport_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:21.293204+00:00
-- url     : https://prove2.me/theorems/379c09a2-8e08-4825-a1bd-73b75003dd90
-- title:
--   Finite Kraus Family: of unitary Transport complete
-- statement:
--   The Finite Kraus Family construction uses the of unitary Transport complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L359-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L359-L367

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteKrausFamily.of_unitaryTransport_complete (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (hE : (E.unitaryTransport U V).Complete) :
    E.Complete := by sorry
