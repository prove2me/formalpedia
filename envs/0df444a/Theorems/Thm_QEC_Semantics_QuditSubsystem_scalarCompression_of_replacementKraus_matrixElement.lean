-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_of_replacementKraus_matrixElement
-- name    : QEC.Semantics.QuditSubsystem.scalarCompression_of_replacementKraus_matrixElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:44.37763+00:00
-- url     : https://prove2.me/theorems/1ea2aa1d-807a-416f-9d82-f5a8eb9d8dcc
-- title:
--   Qudit Subsystem: scalar Compression of replacement Kraus matrix Element
-- statement:
--   A matrix-element KL equation gives scalar compression of the corresponding Kraus product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1269-L1299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1269-L1299

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

theorem QEC.Semantics.QuditSubsystem.scalarCompression_of_replacementKraus_matrixElement
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    {scalar :
        (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
          (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
            Complex}
    (hMatrix : ∀ p r,
      ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
        ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
          inner Complex ((S.replacementKraus rho).operator p x)
            ((S.replacementKraus rho).operator r y) =
            scalar p r * inner Complex x y)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    ScalarCompression C
      ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
        ((S.replacementKraus rho).operator r)) := by sorry
