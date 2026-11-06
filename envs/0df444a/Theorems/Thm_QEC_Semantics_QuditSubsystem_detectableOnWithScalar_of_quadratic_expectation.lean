-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_detectableOnWithScalar_of_quadratic_expectation
-- name    : QEC.Semantics.QuditSubsystem.detectableOnWithScalar_of_quadratic_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:22.365141+00:00
-- url     : https://prove2.me/theorems/61d65158-ae7d-41eb-bc1d-07836cec321b
-- title:
--   Qudit Subsystem: detectable On With Scalar of quadratic expectation
-- statement:
--   Constant pure-state expectations on a nonzero code subspace give detectability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L333-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L333-L372

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

theorem QEC.Semantics.QuditSubsystem.detectableOnWithScalar_of_quadratic_expectation
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hQuadratic : ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
      inner Complex x (A x) = alpha * inner Complex x x) :
    DetectableOnWithScalar C A alpha := by sorry
