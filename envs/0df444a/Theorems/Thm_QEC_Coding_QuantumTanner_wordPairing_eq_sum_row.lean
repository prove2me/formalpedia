-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_wordPairing_eq_sum_row
-- name    : QEC.Coding.QuantumTanner.wordPairing_eq_sum_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:38.000473+00:00
-- url     : https://prove2.me/theorems/05d7da5c-f741-4a69-9327-41046ce42207
-- title:
--   Quantum Tanner: word Pairing eq sum row
-- statement:
--   The global pairing is the sum of its row pairings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L48-L50

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.wordPairing_eq_sum_row (x y : Word F (A × B)) :
    wordPairing x y = ∑ a : A, wordPairing (rowRestriction a x) (rowRestriction a y) := by sorry
