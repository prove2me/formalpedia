-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
-- name    : QEC.Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:10:07.240456+00:00
-- url     : https://prove2.me/theorems/1c93ec76-4ce4-48a6-b34b-cc66991114d7
-- title:
--   Qudit Subsystem: partial Trace Right Raw rank One tmul
-- statement:
--   The raw partial trace of a rank-one tensor operator contracts its right factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L64-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L64-L84

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

theorem QEC.Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k k' : K) :
    partialTraceRightRaw H K
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k) (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex k' k) • (InnerProductSpace.rankOne Complex h h').toLinearMap := by sorry
