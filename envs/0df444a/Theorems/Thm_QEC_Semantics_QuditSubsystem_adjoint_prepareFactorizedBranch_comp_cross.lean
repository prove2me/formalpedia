-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_prepareFactorizedBranch_comp_cross
-- name    : QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_comp_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:08.394142+00:00
-- url     : https://prove2.me/theorems/9ec84f55-b896-452b-974c-8a858c2a9032
-- title:
--   Qudit Subsystem: adjoint prepare Factorized Branch comp cross
-- statement:
--   The Qudit Subsystem construction uses the adjoint prepare Factorized Branch comp cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L789-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L789-L802

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

theorem QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_comp_cross (S : QuditSubsystem q)
    (u v : S.selectedSystem) :
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
      (S.prepareFactorizedBranch v) =
      (inner Complex u v) • (1 : Operator S.complementSystem) := by sorry
