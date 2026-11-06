-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_complete
-- name    : QEC.Semantics.QuditSubsystem.erasureKraus_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:55:09.635517+00:00
-- url     : https://prove2.me/theorems/0879a826-69a5-4c12-9e74-298a2675a7c8
-- title:
--   Qudit Subsystem: erasure Kraus complete
-- statement:
--   The Qudit Subsystem construction uses the erasure Kraus complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L280-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L280-L312

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

theorem QEC.Semantics.QuditSubsystem.erasureKraus_complete (S : QuditSubsystem q) :
    (S.erasureKraus).Complete := by sorry
