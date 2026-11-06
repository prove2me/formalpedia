-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
-- name    : QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:08:47.312128+00:00
-- url     : https://prove2.me/theorems/0f78433c-d4e4-4f2c-9e1b-425fc83bf382
-- title:
--   Finite Subsystem: extend Local apply local Embedding
-- statement:
--   The Finite Subsystem construction uses the extend Local apply local Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L177-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L177-L180

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) (h : S.selectedSystem) :
    S.extendLocal A (S.localEmbedding h) = S.localEmbedding (A h) := by sorry
