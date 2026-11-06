-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_prepareFactorizedBranch_apply_tmul
-- name    : QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:32.700405+00:00
-- url     : https://prove2.me/theorems/a108c573-aee9-454e-b262-dca792170b40
-- title:
--   Qudit Subsystem: adjoint prepare Factorized Branch apply tmul
-- statement:
--   The Qudit Subsystem construction uses the adjoint prepare Factorized Branch apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L733-L741
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L733-L741

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

theorem QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_apply_tmul (S : QuditSubsystem q)
    (u h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.prepareFactorizedBranch u) (h ⊗ₜ[Complex] k) =
      (inner Complex u h) • k := by sorry
