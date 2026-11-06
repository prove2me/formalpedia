-- Prove2me | Theorems.Thm_QEC_Semantics_exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- name    : QEC.Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:17:45.76079+00:00
-- url     : https://prove2.me/theorems/ee9549f3-bc09-442d-aa3b-f6dfbf65ebff
-- title:
--   Semantics: exists finite Kraus Correctable iff exists correctable to Quantum Channel
-- statement:
--   Existential finite-Kraus correctability is exactly existence of completeness and
--   a bundled-channel `Correctable` recovery for the induced CPTP channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L449-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L449-L467

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section

theorem QEC.Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
    {ι : Type v} [Fintype ι] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K) :
    (∃ recovery : QuantumChannel K H,
        FiniteKrausCorrectable ι H K C noise recovery) ↔
      ∃ hnoise : noise.Complete,
        ∃ recovery : QuantumChannel K H,
          Correctable H K C (noise.toQuantumChannel hnoise) recovery := by sorry
