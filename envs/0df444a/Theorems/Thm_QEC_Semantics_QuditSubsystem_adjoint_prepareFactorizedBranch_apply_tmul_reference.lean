-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_prepareFactorizedBranch_apply_tmul_reference
-- name    : QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_apply_tmul_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:47.151717+00:00
-- url     : https://prove2.me/theorems/3d83cbf1-3ba9-4a4a-8dc8-6997ea1efada
-- title:
--   Qudit Subsystem: adjoint prepare Factorized Branch apply tmul reference
-- statement:
--   The Qudit Subsystem construction uses the adjoint prepare Factorized Branch apply tmul reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L242-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L242-L249

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

theorem QEC.Semantics.QuditSubsystem.adjoint_prepareFactorizedBranch_apply_tmul_reference
    (S : QuditSubsystem q) (u h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.prepareFactorizedBranch u) (h ⊗ₜ[Complex] k) =
      (inner Complex u h) • k := by sorry
