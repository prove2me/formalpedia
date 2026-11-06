-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_adjoint_comp
-- name    : QEC.Semantics.QuditSubsystem.replacementKraus_adjoint_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:17.437617+00:00
-- url     : https://prove2.me/theorems/48476d5c-256c-4a8a-8dd7-7de6dbc17f18
-- title:
--   Qudit Subsystem: replacement Kraus adjoint comp
-- statement:
--   The Qudit Subsystem construction uses the replacement Kraus adjoint comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1141-L1175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1141-L1175

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
set_option maxHeartbeats 800000

theorem QEC.Semantics.QuditSubsystem.replacementKraus_adjoint_comp (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
      ((S.replacementKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by sorry
