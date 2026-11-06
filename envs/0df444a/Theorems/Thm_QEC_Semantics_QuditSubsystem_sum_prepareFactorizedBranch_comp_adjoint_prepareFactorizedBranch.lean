-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
-- name    : QEC.Semantics.QuditSubsystem.sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:17.210315+00:00
-- url     : https://prove2.me/theorems/96d586f4-e853-4411-b2cf-f02ef57850ea
-- title:
--   Qudit Subsystem: sum prepare Factorized Branch comp adjoint prepare Factorized Branch
-- statement:
--   Preparation branches for an orthonormal basis resolve the factorized identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L761-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L761-L785

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

theorem QEC.Semantics.QuditSubsystem.sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
    (S : QuditSubsystem q) {κ : Type v} [Fintype κ]
    (b : OrthonormalBasis κ Complex S.selectedSystem) :
    ∑ a : κ, (S.prepareFactorizedBranch (b a)).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch (b a))) = 1 := by sorry
