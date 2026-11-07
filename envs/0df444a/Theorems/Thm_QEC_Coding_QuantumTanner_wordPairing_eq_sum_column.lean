-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_wordPairing_eq_sum_column
-- name    : QEC.Coding.QuantumTanner.wordPairing_eq_sum_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:32.322543+00:00
-- url     : https://prove2.me/theorems/3b48ad71-2054-4136-ac92-f6d106c35be4
-- title:
--   Quantum Tanner: word Pairing eq sum column
-- statement:
--   The global pairing is the sum of its column pairings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L41-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L41-L45

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.wordPairing_eq_sum_column (x y : Word F (A × B)) :
    wordPairing x y = ∑ b : B, wordPairing (columnRestriction b x) (columnRestriction b y) := by sorry
