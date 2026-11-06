-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedPartialTraceFromRegister_trace_pairing
-- name    : QEC.Semantics.QuditSubsystem.selectedPartialTraceFromRegister_trace_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:02.227326+00:00
-- url     : https://prove2.me/theorems/ba8e85e1-c418-4b1a-b9b5-d456f0f5270b
-- title:
--   Qudit Subsystem: selected Partial Trace From Register trace pairing
-- statement:
--   The Qudit Subsystem construction uses the selected Partial Trace From Register trace pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L805-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L805-L829

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

theorem QEC.Semantics.QuditSubsystem.selectedPartialTraceFromRegister_trace_pairing (S : QuditSubsystem q)
    (A : Operator (Qudit.QuditRegister q)) (X : Operator S.selectedSystem) :
    LinearMap.trace Complex S.selectedSystem
      ((S.selectedPartialTraceFromRegister A).comp X) =
      LinearMap.trace Complex (Qudit.QuditRegister q)
        (A.comp (S.extendLocalToRegister X)) := by sorry
