-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
-- name    : QEC.Semantics.QuditSubsystem.selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:08.557195+00:00
-- url     : https://prove2.me/theorems/90c4fa71-6622-4e47-a276-0d9319f7f44f
-- title:
--   Qudit Subsystem: selected Partial Trace From Register rank One eq smul selected Marginal
-- statement:
--   The Qudit Subsystem construction uses the selected Partial Trace From Register rank One eq smul selected Marginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L892-L953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L892-L953

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho)
    (x y : Qudit.QuditRegister q) (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) :
    S.selectedPartialTraceFromRegister
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator := by sorry
