-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_allLocalScalarCompression_of_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.allLocalScalarCompression_of_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:01.848181+00:00
-- url     : https://prove2.me/theorems/6deffecc-77db-499c-b691-40bba429fd09
-- title:
--   Qudit Subsystem: all Local Scalar Compression of rank One basis
-- statement:
--   Scalar compression of a local matrix-unit basis extends to all local operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L538-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L538-L554

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

theorem QEC.Semantics.QuditSubsystem.allLocalScalarCompression_of_rankOne_basis
    {C : QuantumCode (Qudit.QuditRegister q)} {S : QuditSubsystem q}
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (hRankOne : ∀ i j : κ,
      ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap)) :
    AllLocalScalarCompression C S := by sorry
