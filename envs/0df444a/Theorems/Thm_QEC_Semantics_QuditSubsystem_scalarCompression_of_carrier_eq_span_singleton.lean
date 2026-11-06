-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_of_carrier_eq_span_singleton
-- name    : QEC.Semantics.QuditSubsystem.scalarCompression_of_carrier_eq_span_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:46.76929+00:00
-- url     : https://prove2.me/theorems/e816a1d8-c133-4bf4-834e-bc52dc39aad7
-- title:
--   Qudit Subsystem: scalar Compression of carrier eq span singleton
-- statement:
--   Every operator has scalar compression to a nonzero one-dimensional code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L603-L615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L603-L615

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

theorem QEC.Semantics.QuditSubsystem.scalarCompression_of_carrier_eq_span_singleton
    (C : QuantumCode (Qudit.QuditRegister q)) (v : Qudit.QuditRegister q)
    (hv : v ≠ 0) (hC : C.carrier = Complex ∙ v)
    (A : Operator (Qudit.QuditRegister q)) : ScalarCompression C A := by sorry
