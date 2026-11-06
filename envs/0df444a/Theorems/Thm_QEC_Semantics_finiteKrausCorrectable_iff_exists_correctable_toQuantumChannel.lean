-- Prove2me | Theorems.Thm_QEC_Semantics_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- name    : QEC.Semantics.finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:33.377299+00:00
-- url     : https://prove2.me/theorems/7062083e-5705-4f46-ab70-743cce7f6a42
-- title:
--   Semantics: finite Kraus Correctable iff exists correctable to Quantum Channel
-- statement:
--   Finite-Kraus correctability is exactly completeness plus ordinary semantic
--   correctability for the induced bundled CPTP channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L429-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L429-L443

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section

theorem QEC.Semantics.finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
    {ι : Type v} [Fintype ι] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K)
    (recovery : QuantumChannel K H) :
    FiniteKrausCorrectable ι H K C noise recovery ↔
      ∃ hnoise : noise.Complete,
        Correctable H K C (noise.toQuantumChannel hnoise) recovery := by sorry
