-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_eq_replacement
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_eq_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:35.840582+00:00
-- url     : https://prove2.me/theorems/e965907c-6f25-4446-80ba-0383390f74e0
-- title:
--   Qudit Subsystem: replacement Factorized Kraus induced Map eq replacement
-- statement:
--   The raw induced map of the explicit family is preparation after factored erasure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1095-L1110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1095-L1110

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_eq_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementFactorizedKraus rho).inducedMap =
      (QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel).toLinearMap := by sorry
