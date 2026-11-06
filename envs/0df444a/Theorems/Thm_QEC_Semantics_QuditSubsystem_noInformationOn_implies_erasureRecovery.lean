-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_erasureRecovery
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_implies_erasureRecovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:35.011451+00:00
-- url     : https://prove2.me/theorems/5852f277-c1e7-475e-9413-92211912f748
-- title:
--   Qudit Subsystem: no Information On implies erasure Recovery
-- statement:
--   No local information yields recovery from the concrete coordinate-erasure channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1256-L1266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1256-L1266

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_implies_erasureRecovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
