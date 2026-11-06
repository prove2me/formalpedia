-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureCorrectable_iff
-- name    : QEC.Semantics.QuditSubsystem.erasureCorrectable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:44.185658+00:00
-- url     : https://prove2.me/theorems/1466a5b1-d6a5-4206-beda-42ece45d5b7f
-- title:
--   Qudit Subsystem: erasure Correctable iff
-- statement:
--   Typed factored qudit erasure correctability is the existing `Correctable` predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L810-L814
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L810-L814

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

theorem QEC.Semantics.QuditSubsystem.erasureCorrectable_iff (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by sorry
