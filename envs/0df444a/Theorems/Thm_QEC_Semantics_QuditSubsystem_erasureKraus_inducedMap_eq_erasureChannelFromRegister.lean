-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_inducedMap_eq_erasureChannelFromRegister
-- name    : QEC.Semantics.QuditSubsystem.erasureKraus_inducedMap_eq_erasureChannelFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:04.93562+00:00
-- url     : https://prove2.me/theorems/201b4974-eb6c-4738-9254-d830d47ef123
-- title:
--   Qudit Subsystem: erasure Kraus induced Map eq erasure Channel From Register
-- statement:
--   The Qudit Subsystem construction uses the erasure Kraus induced Map eq erasure Channel From Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L455-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L455-L465

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

theorem QEC.Semantics.QuditSubsystem.erasureKraus_inducedMap_eq_erasureChannelFromRegister (S : QuditSubsystem q) :
    S.erasureKraus.inducedMap = S.erasureChannelFromRegister.toLinearMap := by sorry
