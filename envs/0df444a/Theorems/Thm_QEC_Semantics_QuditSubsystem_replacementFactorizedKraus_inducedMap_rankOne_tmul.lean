-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_rankOne_tmul
-- name    : QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:22.600253+00:00
-- url     : https://prove2.me/theorems/27331cfc-d83e-41ba-a138-29ea044f9722
-- title:
--   Qudit Subsystem: replacement Factorized Kraus induced Map rank One tmul
-- statement:
--   The replacement family has the expected action on product-basis matrix units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L983-L1053
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L983-L1053

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

theorem QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
  if a = b then ∑ i : Fin (S.densityEnsembleSize rho),
        (InnerProductSpace.rankOne Complex
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] k)
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] l)).toLinearMap else 0 := by sorry
