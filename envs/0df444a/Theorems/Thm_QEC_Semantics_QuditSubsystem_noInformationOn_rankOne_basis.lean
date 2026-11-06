-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:30.573177+00:00
-- url     : https://prove2.me/theorems/0fa97163-e5ac-423a-b379-7f32427e5db7
-- title:
--   Qudit Subsystem: no Information On rank One basis
-- statement:
--   Effect-level no-information gives scalar compression of every local matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L450-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L450-L515

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_rankOne_basis
    {C : QuantumCode (Qudit.QuditRegister q)} {S : QuditSubsystem q}
    (hInformation : NoInformationOn C S)
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (i j : κ) :
    ScalarCompression C
      (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) := by sorry
