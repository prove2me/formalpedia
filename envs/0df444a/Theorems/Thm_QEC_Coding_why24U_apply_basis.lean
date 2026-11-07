-- Prove2me | Theorems.Thm_QEC_Coding_why24U_apply_basis
-- name    : QEC.Coding.why24U_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:27:42.742396+00:00
-- url     : https://prove2.me/theorems/e9e4e070-41b0-471b-8c7a-3ee7d0f21207
-- title:
--   Coding: why24 U apply basis
-- statement:
--   Source-exact action of `U_β^(n)` on a concrete computational-basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L90-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L90-L99

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_apply_basis (β : F1024) (n : ℕ) (η : F1024) :
    why24U β n (why24QuditComputationalBasis η) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) •
        why24QuditComputationalBasis η := by sorry
