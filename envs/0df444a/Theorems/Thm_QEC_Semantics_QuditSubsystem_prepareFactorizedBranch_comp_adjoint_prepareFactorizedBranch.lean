-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
-- name    : QEC.Semantics.QuditSubsystem.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:52.859538+00:00
-- url     : https://prove2.me/theorems/378197ea-da23-4c36-a5a3-e16b53bdd4df
-- title:
--   Qudit Subsystem: prepare Factorized Branch comp adjoint prepare Factorized Branch
-- statement:
--   A preparation branch followed by its adjoint is the corresponding local matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L744-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L744-L758

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

theorem QEC.Semantics.QuditSubsystem.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
    (S : QuditSubsystem q) (u v : S.selectedSystem) :
    (S.prepareFactorizedBranch u).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch v)) =
      S.extendLocal (InnerProductSpace.rankOne Complex u v).toLinearMap := by sorry
