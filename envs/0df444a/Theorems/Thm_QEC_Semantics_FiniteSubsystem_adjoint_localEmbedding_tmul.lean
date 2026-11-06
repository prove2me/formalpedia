-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_adjoint_localEmbedding_tmul
-- name    : QEC.Semantics.FiniteSubsystem.adjoint_localEmbedding_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:11.314379+00:00
-- url     : https://prove2.me/theorems/e2d41fec-6fee-45cd-99d4-879cc4c4456c
-- title:
--   Finite Subsystem: adjoint local Embedding tmul
-- statement:
--   The Finite Subsystem construction uses the adjoint local Embedding tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L157-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L157-L164

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

theorem QEC.Semantics.FiniteSubsystem.adjoint_localEmbedding_tmul (S : FiniteSubsystem ι)
    (h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint S.localEmbedding (h ⊗ₜ[Complex] k) =
      (inner Complex S.complementAnchor k) • h := by sorry
