-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
-- name    : QEC.Semantics.QuditSubsystem.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:48.511371+00:00
-- url     : https://prove2.me/theorems/f4bb173c-d063-4e59-90ef-1d27ef649e24
-- title:
--   Qudit Subsystem: prepare Factorized Branch comp adjoint prepare Factorized Branch reference
-- statement:
--   The Qudit Subsystem construction uses the prepare Factorized Branch comp adjoint prepare Factorized Branch reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L252-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L252-L267

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
    (S : QuditSubsystem q) (u v : S.selectedSystem) :
    (S.prepareFactorizedBranch u).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch v)) =
      S.extendLocal (InnerProductSpace.rankOne Complex u v).toLinearMap := by sorry
