-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_matrixElementKL_of_allLocalScalarCompression
-- name    : QEC.Semantics.QuditSubsystem.replacementKraus_matrixElementKL_of_allLocalScalarCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:35.346887+00:00
-- url     : https://prove2.me/theorems/220401e3-04ba-4e4c-ab35-48da51d2d571
-- title:
--   Qudit Subsystem: replacement Kraus matrix Element KL of all Local Scalar Compression
-- statement:
--   Local scalar compression supplies the matrix-element KL equations for the explicit replacement family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1199-L1234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1199-L1234

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

theorem QEC.Semantics.QuditSubsystem.replacementKraus_matrixElementKL_of_allLocalScalarCompression
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hLocal : AllLocalScalarCompression C S) :
    ∃ scalar :
        (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
          (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
            Complex,
      ∀ p r,
        ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
          ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
            inner Complex ((S.replacementKraus rho).operator p x)
              ((S.replacementKraus rho).operator r y) =
              scalar p r * inner Complex x y := by sorry
