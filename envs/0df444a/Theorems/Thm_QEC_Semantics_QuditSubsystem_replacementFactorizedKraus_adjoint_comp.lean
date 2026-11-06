-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_adjoint_comp
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_adjoint_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:51.316119+00:00
-- url     : https://prove2.me/theorems/82a03dbb-4549-49e6-8d0f-b915e9b670e5
-- title:
--   Qudit Subsystem: replacement Factorized Kraus adjoint comp
-- statement:
--   Cross products of replacement branches are selected local matrix units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L831-L879
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L831-L879

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_adjoint_comp (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator p)).comp
      ((S.replacementFactorizedKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by sorry
