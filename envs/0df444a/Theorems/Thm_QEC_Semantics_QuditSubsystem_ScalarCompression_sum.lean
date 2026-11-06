-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
-- name    : QEC.Semantics.QuditSubsystem.ScalarCompression.sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:27.529775+00:00
-- url     : https://prove2.me/theorems/8244eb60-65dd-4cbe-9e8c-b98eea9ad6d5
-- title:
--   Scalar Compression: sum
-- statement:
--   Scalar compression is closed under finite sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L249-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L249-L257

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

theorem QEC.Semantics.QuditSubsystem.ScalarCompression.sum
    {C : QuantumCode (Qudit.QuditRegister q)} {κ : Type v} [Fintype κ]
    (f : κ → Operator (Qudit.QuditRegister q))
    (h : ∀ i, ScalarCompression C (f i)) : ScalarCompression C (∑ i, f i) := by sorry
