-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_complete
-- name    : QEC.Semantics.QuditSubsystem.replacementKraus_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:09.533542+00:00
-- url     : https://prove2.me/theorems/592131c1-25e4-4d08-a6f3-c7828b917be0
-- title:
--   Qudit Subsystem: replacement Kraus complete
-- statement:
--   The global transported replacement family remains complete.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1132-L1137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1132-L1137

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

theorem QEC.Semantics.QuditSubsystem.replacementKraus_complete (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementKraus rho).Complete := by sorry
