-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_erasure_fixed_of_supportedOn_branch
-- name    : QEC.Semantics.QuditSubsystem.prepareFactorized_erasure_fixed_of_supportedOn_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:58:50.253976+00:00
-- url     : https://prove2.me/theorems/c4303997-cf98-4835-b639-bc9b0e5f3e2b
-- title:
--   Qudit Subsystem: prepare Factorized erasure fixed of supported On branch
-- statement:
--   An operator-valued density supported on the range of a normalized preparation
--   branch is fixed by concrete erasure followed by preparation of that branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1329-L1401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1329-L1401

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

theorem QEC.Semantics.QuditSubsystem.prepareFactorized_erasure_fixed_of_supportedOn_branch
    (S : QuditSubsystem q) (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1)
    (rho : DensityOperator S.factorizedSystem)
    (hsupported : ∀ z : S.factorizedSystem,
      rho.toOperator z ∈ LinearMap.range (S.prepareFactorizedBranch u)) :
    S.prepareFactorized (pureDensity u hu) (S.erasureChannel rho.toOperator) =
      rho.toOperator := by sorry
