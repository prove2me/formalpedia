-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:17.366113+00:00
-- url     : https://prove2.me/theorems/58f5bc65-4e30-4797-aef3-61c01b18ecf8
-- title:
--   Qudit Subsystem: replacement Factorized Kraus operator
-- statement:
--   The Qudit Subsystem construction uses the replacement Factorized Kraus operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L821-L828
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L821-L828

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (S.replacementFactorizedKraus rho).operator p =
      (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2))) := by sorry

attribute [defeq] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
