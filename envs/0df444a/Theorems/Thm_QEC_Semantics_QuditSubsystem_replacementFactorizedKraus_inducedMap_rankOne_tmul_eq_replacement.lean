-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:26.955246+00:00
-- url     : https://prove2.me/theorems/2e8b3a9a-3a3d-431c-8579-35f415a2d7dd
-- title:
--   Qudit Subsystem: replacement Factorized Kraus induced Map rank One tmul eq replacement
-- statement:
--   The explicit replacement family agrees with preparation after concrete factored erasure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1069-L1092
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1069-L1092

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
      S.prepareFactorized rho
        (S.erasureChannel
          (InnerProductSpace.rankOne Complex
            (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
            (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap) := by sorry
