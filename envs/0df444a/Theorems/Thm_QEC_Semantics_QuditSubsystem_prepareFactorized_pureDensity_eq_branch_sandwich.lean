-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_pureDensity_eq_branch_sandwich
-- name    : QEC.Semantics.QuditSubsystem.prepareFactorized_pureDensity_eq_branch_sandwich
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:40.128196+00:00
-- url     : https://prove2.me/theorems/da5e734a-1214-4adb-bd93-5f440adb0486
-- title:
--   Qudit Subsystem: prepare Factorized pure Density eq branch sandwich
-- statement:
--   Pure selected preparation is the concrete isometric branch sandwich.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1307-L1323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1307-L1323

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

theorem QEC.Semantics.QuditSubsystem.prepareFactorized_pureDensity_eq_branch_sandwich (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareFactorized (pureDensity u hu) A =
      (S.prepareFactorizedBranch u).comp
        (A.comp (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by sorry
