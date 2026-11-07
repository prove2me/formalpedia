-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditZ_apply
-- name    : QEC.Coding.why24QuditZ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:24.638014+00:00
-- url     : https://prove2.me/theorems/cf597ee8-7333-42e0-93b4-7e00b4ce4626
-- title:
--   Coding: why24 Qudit Z apply
-- statement:
--   The Coding construction uses the why24 Qudit Z apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L135-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L135-L138

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditZ_apply (γ : F1024) (ψ : Why24QuditSpace) (η : F1024) :
    why24QuditZ γ ψ η =
      PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (γ * η)) * ψ η := by sorry

attribute [defeq] QEC.Coding.why24QuditZ_apply
