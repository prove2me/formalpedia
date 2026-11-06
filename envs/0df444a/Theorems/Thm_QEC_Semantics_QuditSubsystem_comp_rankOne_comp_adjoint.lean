-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_comp_rankOne_comp_adjoint
-- name    : QEC.Semantics.QuditSubsystem.comp_rankOne_comp_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:34.75104+00:00
-- url     : https://prove2.me/theorems/9d38c8ee-7efc-44dd-9703-b36765054856
-- title:
--   Qudit Subsystem: comp rank One comp adjoint
-- statement:
--   A Kraus sandwich maps a rank-one operator to the rank one of its images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L973-L980
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L973-L980

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

theorem QEC.Semantics.QuditSubsystem.comp_rankOne_comp_adjoint (S : QuditSubsystem q)
    (K : Operator S.factorizedSystem) (x y : S.factorizedSystem) :
    K.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
      (LinearMap.adjoint K)) =
      (InnerProductSpace.rankOne Complex (K x) (K y)).toLinearMap := by sorry
