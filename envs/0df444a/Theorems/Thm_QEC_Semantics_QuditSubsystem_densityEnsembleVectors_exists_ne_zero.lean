-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_densityEnsembleVectors_exists_ne_zero
-- name    : QEC.Semantics.QuditSubsystem.densityEnsembleVectors_exists_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:40.61957+00:00
-- url     : https://prove2.me/theorems/137a58a7-50cc-4e35-8b1a-063a64ce1608
-- title:
--   Qudit Subsystem: density Ensemble Vectors exists ne zero
-- statement:
--   A normalized finite rank-one ensemble contains a nonzero branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1302-L1315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1302-L1315

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

theorem QEC.Semantics.QuditSubsystem.densityEnsembleVectors_exists_ne_zero (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∃ i : Fin (S.densityEnsembleSize rho), S.densityEnsembleVectors rho i ≠ 0 := by sorry
