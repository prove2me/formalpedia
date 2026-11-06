-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecoverable_iff_exists_correctable
-- name    : QEC.Semantics.QuditSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:47:03.196556+00:00
-- url     : https://prove2.me/theorems/d467e417-4266-496c-8fa8-3a099b26a556
-- title:
--   Qudit Subsystem: erasure Recoverable iff exists correctable
-- statement:
--   Existential factored erasure recoverability stays in the CPTP channel vocabulary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L837-L842
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L837-L842

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

theorem QEC.Semantics.QuditSubsystem.erasureRecoverable_iff_exists_correctable (S : QuditSubsystem q)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by sorry
