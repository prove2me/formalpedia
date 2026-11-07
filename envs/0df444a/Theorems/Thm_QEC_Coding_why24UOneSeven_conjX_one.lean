-- Prove2me | Theorems.Thm_QEC_Coding_why24UOneSeven_conjX_one
-- name    : QEC.Coding.why24UOneSeven_conjX_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:23.958412+00:00
-- url     : https://prove2.me/theorems/0a6d136f-20e4-466b-8d70-7c0d6e9d927f
-- title:
--   Coding: why24 UOne Seven conj X one
-- statement:
--   The source's displayed `γ = 1` seventh-power conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L946-L953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L946-L953

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24UOneSeven_conjX_one :
    why24UOneSeven * why24QuditX (1 : F1024) * LinearMap.adjoint why24UOneSeven =
      PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) ^ 7)) •
        (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 * why24QuditZ (1 : F1024)) := by sorry
