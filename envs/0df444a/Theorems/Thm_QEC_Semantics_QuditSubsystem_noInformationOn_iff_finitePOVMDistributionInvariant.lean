-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_finitePOVMDistributionInvariant
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_iff_finitePOVMDistributionInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:18:18.164342+00:00
-- url     : https://prove2.me/theorems/e5fad171-c399-491b-9363-762f62a43b63
-- title:
--   Qudit Subsystem: no Information On iff finite POVMDistribution Invariant
-- statement:
--   Effect-level no-information is equivalent to finite-POVM distribution invariance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L680-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L680-L689

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_iff_finitePOVMDistributionInvariant
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ FinitePOVMDistributionInvariant.{u, v} C S := by sorry
