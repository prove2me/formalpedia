-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_replacementAfterErasureWith_recovery
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_implies_replacementAfterErasureWith_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:35.583922+00:00
-- url     : https://prove2.me/theorems/e968ac59-5a3f-4818-983d-b17576e01b8e
-- title:
--   Qudit Subsystem: no Information On implies replacement After Erasure With recovery
-- statement:
--   No local information yields a CPTP recovery for any normalized replacement-after-erasure channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1237-L1253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1237-L1253

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_implies_replacementAfterErasureWith_recovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasureWith rho) recovery := by sorry
