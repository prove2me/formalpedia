-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_pureOfNonzero
-- name    : QEC.Semantics.QuditSubsystem.trace_comp_pureOfNonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:28.51828+00:00
-- url     : https://prove2.me/theorems/03445b1d-cd43-4dad-b660-4effd65a70f4
-- title:
--   Qudit Subsystem: trace comp pure Of Nonzero
-- statement:
--   The outcome trace of an operator on a normalized pure density is its Rayleigh quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L308-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L308-L330

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

theorem QEC.Semantics.QuditSubsystem.trace_comp_pureOfNonzero
    (A : Operator (Qudit.QuditRegister q)) (x : Qudit.QuditRegister q) (hx : x ≠ 0) :
    LinearMap.trace Complex (Qudit.QuditRegister q)
      (A.comp (DensityOperator.pureOfNonzero x hx).toOperator) =
      (inner Complex x x)⁻¹ * inner Complex x (A x) := by sorry
