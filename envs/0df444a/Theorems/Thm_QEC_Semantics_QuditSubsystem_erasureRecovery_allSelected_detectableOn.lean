-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_allSelected_detectableOn
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_allSelected_detectableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:59.198351+00:00
-- url     : https://prove2.me/theorems/f740e143-c00d-4e7d-80c4-01beeee51194
-- title:
--   Qudit Subsystem: erasure Recovery all Selected detectable On
-- statement:
--   The Qudit Subsystem construction uses the erasure Recovery all Selected detectable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L649-L688
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L649-L688

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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_allSelected_detectableOn (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (A : Operator S.selectedSystem) :
    DetectableOn C (S.extendLocalToRegister A) := by sorry
