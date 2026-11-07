-- Prove2me | Theorems.Thm_QEC_Coding_why24U_apply
-- name    : QEC.Coding.why24U_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:19:25.24854+00:00
-- url     : https://prove2.me/theorems/b13581a5-03df-4607-a29b-e5e188fab555
-- title:
--   Coding: why24 U apply
-- statement:
--   The Coding construction uses the why24 U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L29-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L29-L34

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_apply (β : F1024) (n : ℕ)
    (ψ : Why24QuditSpace) (η : F1024) :
    why24U β n ψ η =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * ψ η := by sorry

attribute [defeq] QEC.Coding.why24U_apply
