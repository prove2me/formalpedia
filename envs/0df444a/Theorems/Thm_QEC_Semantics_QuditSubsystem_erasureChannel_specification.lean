-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_specification
-- name    : QEC.Semantics.QuditSubsystem.erasureChannel_specification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:34.134623+00:00
-- url     : https://prove2.me/theorems/f40e50cc-dcc0-459d-b522-90c843ca3edf
-- title:
--   Qudit Subsystem: erasure Channel specification
-- statement:
--   The factored erasure channel is exactly factor swap followed by raw CPTP partial trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L471-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L471-L476

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.erasureChannel_specification (S : QuditSubsystem q) :
    S.erasureChannel =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
        (QuantumChannel.unitaryConj S.factorSwap) := by sorry
