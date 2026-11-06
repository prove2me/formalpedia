-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_noInformationOn
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_implies_noInformationOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:50.31707+00:00
-- url     : https://prove2.me/theorems/bc46f33a-6ce0-4350-a299-927f07071723
-- title:
--   Qudit Subsystem: erasure Recovery implies no Information On
-- statement:
--   A concrete erasure recovery makes every local valid effect information-free on the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1318-L1354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1318-L1354

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_implies_noInformationOn
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hRecovery : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    NoInformationOn C S := by sorry
