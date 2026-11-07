-- Prove2me | Theorems.Thm_QEC_Coding_why24U_conjX_five
-- name    : QEC.Coding.why24U_conjX_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:19:47.428093+00:00
-- url     : https://prove2.me/theorems/f7709a9c-e404-49b0-8b9e-1dc3d610c533
-- title:
--   Coding: why24 U conj X five
-- statement:
--   Source-derived conjugation of a concrete field shift by `U_β^(5)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L275-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L275-L310

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_conjX_five (β γ : F1024) :
    why24U β 5 * why24QuditX γ * LinearMap.adjoint (why24U β 5) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)) •
        (why24QuditX γ *
          why24QuditZ (why24FrobeniusRootFour (β * γ) + β * γ ^ 4)) := by sorry
