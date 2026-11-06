-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctedBy_iff_correctable_toQuantumChannel
-- name    : QEC.Semantics.FiniteKrausFamily.correctedBy_iff_correctable_toQuantumChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:26:12.882592+00:00
-- url     : https://prove2.me/theorems/713c0ae5-67a5-4e1f-8b9a-df5ba5ebecfd
-- title:
--   Finite Kraus Family: corrected By iff correctable to Quantum Channel
-- statement:
--   Correcting the raw induced finite-Kraus map is the same as correcting the
--   bundled CPTP channel obtained from a complete finite Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L403-L407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L403-L407

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
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

theorem QEC.Semantics.FiniteKrausFamily.correctedBy_iff_correctable_toQuantumChannel
    (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (C : QuantumCode H) (recovery : QuantumChannel K H) :
    E.CorrectedBy C recovery ↔ Correctable H K C (E.toQuantumChannel hE) recovery := by sorry
