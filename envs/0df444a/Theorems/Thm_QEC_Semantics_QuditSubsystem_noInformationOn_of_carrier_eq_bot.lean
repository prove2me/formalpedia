-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_of_carrier_eq_bot
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:22.017181+00:00
-- url     : https://prove2.me/theorems/52e1b45f-bd6f-4481-aa86-56dbc1937238
-- title:
--   Qudit Subsystem: no Information On of carrier eq bot
-- statement:
--   A code with bottom carrier has zero projector and therefore no local information.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L589-L600
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L589-L600

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_bot
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (hC : C.carrier = ⊥) : NoInformationOn C S := by sorry
