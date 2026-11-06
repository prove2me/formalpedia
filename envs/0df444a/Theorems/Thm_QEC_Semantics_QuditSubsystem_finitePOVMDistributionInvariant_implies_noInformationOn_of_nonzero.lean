-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero
-- name    : QEC.Semantics.QuditSubsystem.finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:49.801619+00:00
-- url     : https://prove2.me/theorems/fcdcfcf9-093f-46f4-b57e-4a9a856d1587
-- title:
--   Qudit Subsystem: finite POVMDistribution Invariant implies no Information On of nonzero
-- statement:
--   On a nonzero code carrier, finite-POVM distribution invariance gives no-information.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L627-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L627-L677

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

theorem QEC.Semantics.QuditSubsystem.finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (hC : C.carrier ≠ ⊥) :
    FinitePOVMDistributionInvariant.{u, v} C S → NoInformationOn C S := by sorry
