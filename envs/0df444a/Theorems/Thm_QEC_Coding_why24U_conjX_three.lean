-- Prove2me | Theorems.Thm_QEC_Coding_why24U_conjX_three
-- name    : QEC.Coding.why24U_conjX_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:30.371119+00:00
-- url     : https://prove2.me/theorems/7547dbf6-db9a-448e-9a26-cca313f42bad
-- title:
--   Coding: why24 U conj X three
-- statement:
--   Source-derived conjugation of a concrete field shift by `U_β^(3)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L194-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L194-L229

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_conjX_three (β γ : F1024) :
    why24U β 3 * why24QuditX γ * LinearMap.adjoint (why24U β 3) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 3)) •
        (why24QuditX γ *
          why24QuditZ (why24FrobeniusRootTwo (β * γ) + β * γ ^ 2)) := by sorry
