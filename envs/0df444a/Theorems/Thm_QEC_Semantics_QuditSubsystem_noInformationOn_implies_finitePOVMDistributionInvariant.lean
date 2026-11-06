-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_finitePOVMDistributionInvariant
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_implies_finitePOVMDistributionInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:40.563413+00:00
-- url     : https://prove2.me/theorems/b4639c02-c59a-49c3-a008-3f483d1c0f05
-- title:
--   Qudit Subsystem: no Information On implies finite POVMDistribution Invariant
-- statement:
--   No-information makes every valid finite-POVM outcome distribution-independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L580-L586
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L580-L586

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_implies_finitePOVMDistributionInvariant
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S → FinitePOVMDistributionInvariant.{u, v} C S := by sorry
