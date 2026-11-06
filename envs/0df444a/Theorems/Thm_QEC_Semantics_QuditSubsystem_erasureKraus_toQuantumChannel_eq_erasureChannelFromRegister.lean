-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_toQuantumChannel_eq_erasureChannelFromRegister
-- name    : QEC.Semantics.QuditSubsystem.erasureKraus_toQuantumChannel_eq_erasureChannelFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:56:45.404975+00:00
-- url     : https://prove2.me/theorems/cd12920a-66b4-449c-b5a6-e56ccfbca2a6
-- title:
--   Qudit Subsystem: erasure Kraus to Quantum Channel eq erasure Channel From Register
-- statement:
--   The Qudit Subsystem construction uses the erasure Kraus to Quantum Channel eq erasure Channel From Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L468-L473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L468-L473

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

theorem QEC.Semantics.QuditSubsystem.erasureKraus_toQuantumChannel_eq_erasureChannelFromRegister
    (S : QuditSubsystem q) (hComplete : S.erasureKraus.Complete) :
    S.erasureKraus.toQuantumChannel hComplete = S.erasureChannelFromRegister := by sorry
