-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
-- name    : QEC.Semantics.QuantumChannel.comp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:46:31.896192+00:00
-- url     : https://prove2.me/theorems/9b1ac647-22d9-411b-830b-d401a511aef1
-- title:
--   Quantum Channel: comp apply
-- statement:
--   The Quantum Channel construction uses the comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L222-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L222-L225

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.QuantumChannel.comp_apply {L : Type u} [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K)
    (A : Operator H) : (comp Ψ Φ) A = Ψ (Φ A) := by sorry

attribute [defeq] QEC.Semantics.QuantumChannel.comp_apply
