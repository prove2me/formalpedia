-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_sum_reference
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_sum_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:49.509024+00:00
-- url     : https://prove2.me/theorems/71d8f5b2-0fbc-4e58-a0c0-b55c4db9d631
-- title:
--   Qudit Subsystem: extend Local To Register sum reference
-- statement:
--   The Qudit Subsystem construction uses the extend Local To Register sum reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L599-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L599-L617

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_sum_reference (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocalToRegister (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocalToRegister (f i) := by sorry
