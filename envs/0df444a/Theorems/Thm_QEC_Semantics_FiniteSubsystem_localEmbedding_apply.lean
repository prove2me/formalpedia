-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
-- name    : QEC.Semantics.FiniteSubsystem.localEmbedding_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:08:19.831086+00:00
-- url     : https://prove2.me/theorems/09f36250-a62d-43dd-9f46-7bd9e0024191
-- title:
--   Finite Subsystem: local Embedding apply
-- statement:
--   The Finite Subsystem construction uses the local Embedding apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L153-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L153-L155

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

theorem QEC.Semantics.FiniteSubsystem.localEmbedding_apply (S : FiniteSubsystem ι) (h : S.selectedSystem) :
    S.localEmbedding h = h ⊗ₜ[Complex] S.complementAnchor := by sorry

attribute [defeq] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
