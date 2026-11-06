-- Prove2me | Theorems.Thm_QEC_Semantics_operator_ext_of_trace_comp_right_eq
-- name    : QEC.Semantics.operator_ext_of_trace_comp_right_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:18:34.441859+00:00
-- url     : https://prove2.me/theorems/911e2a50-1f01-4d32-8aea-913b6b01a53a
-- title:
--   Semantics: operator ext of trace comp right eq
-- statement:
--   Operators are separated by right trace pairings against all test operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L45-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L45-L58

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.operator_ext_of_trace_comp_right_eq {S T : Operator H}
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex H (A.comp S) = LinearMap.trace Complex H (A.comp T)) :
    S = T := by sorry
