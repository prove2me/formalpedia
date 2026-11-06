-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator_apply_basis_tmul
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator_apply_basis_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:26.194069+00:00
-- url     : https://prove2.me/theorems/6e495d52-bb16-45ac-bb8c-f23dbd17f651
-- title:
--   Qudit Subsystem: replacement Factorized Kraus operator apply basis tmul
-- statement:
--   A replacement branch selects exactly its matching selected basis component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L956-L970
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L956-L970

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator_apply_basis_tmul (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
    (a : Fin (Module.finrank Complex S.selectedSystem)) (k : S.complementSystem) :
    (S.replacementFactorizedKraus rho).operator p
      (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k) =
      if p.2 = a then (S.densityEnsembleVectors rho p.1) ⊗ₜ[Complex] k else 0 := by sorry
