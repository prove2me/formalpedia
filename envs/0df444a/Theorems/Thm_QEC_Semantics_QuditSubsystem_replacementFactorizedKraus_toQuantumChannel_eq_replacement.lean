-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_toQuantumChannel_eq_replacement
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_toQuantumChannel_eq_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:31:28.63534+00:00
-- url     : https://prove2.me/theorems/7e8116d3-4766-42db-92d8-ce09ee380c88
-- title:
--   Qudit Subsystem: replacement Factorized Kraus to Quantum Channel eq replacement
-- statement:
--   The complete explicit replacement family packages the factorized replacement channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1113-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1113-L1120

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_toQuantumChannel_eq_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (hComplete : (S.replacementFactorizedKraus rho).Complete) :
    (S.replacementFactorizedKraus rho).toQuantumChannel hComplete =
      QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel := by sorry
