-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctable_id_of_carrier_eq_bot
-- name    : QEC.Semantics.FiniteKrausFamily.correctable_id_of_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:15:20.117188+00:00
-- url     : https://prove2.me/theorems/25c726f6-30bb-4b19-9505-8bcac97d1869
-- title:
--   Finite Kraus Family: correctable id of carrier eq bot
-- statement:
--   If the code carrier is empty, the semantic correction obligation is vacuous.
--
--   This lemma isolates the degenerate branch of the KL-implies-correctable proof:
--   no density operator can have trace one and range in the bottom carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L155-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L155-L171

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.correctable_id_of_carrier_eq_bot
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete) (hC : C.carrier = ⊥) :
    Correctable H H C (E.toQuantumChannel hE) (QuantumChannel.id H) := by sorry
