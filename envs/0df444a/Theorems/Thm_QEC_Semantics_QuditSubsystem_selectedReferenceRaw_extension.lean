-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceRaw_extension
-- name    : QEC.Semantics.QuditSubsystem.selectedReferenceRaw_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:11.809591+00:00
-- url     : https://prove2.me/theorems/c6c452a8-c768-412d-b6e3-083733d10660
-- title:
--   Qudit Subsystem: selected Reference Raw extension
-- statement:
--   The Qudit Subsystem construction uses the selected Reference Raw extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1047-L1210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1047-L1210

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
set_option maxHeartbeats 800000

theorem QEC.Semantics.QuditSubsystem.selectedReferenceRaw_extension (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref] (A : Operator (Qudit.QuditRegister q))
    (r s : Ref) :
    partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      ((S.selectedReferenceTransport Ref).conjOperator
        (TensorProduct.map A (InnerProductSpace.rankOne Complex r s).toLinearMap)) =
      TensorProduct.map (S.selectedPartialTraceFromRegister A)
        (InnerProductSpace.rankOne Complex r s).toLinearMap := by sorry
