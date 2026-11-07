-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_wordPairing_columnExtension
-- name    : QEC.Coding.QuantumTanner.wordPairing_columnExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:18.666224+00:00
-- url     : https://prove2.me/theorems/49ee5f33-e1e2-4185-8d0c-814f14b06eae
-- title:
--   Quantum Tanner: word Pairing column Extension
-- statement:
--   The Quantum Tanner construction uses the word Pairing column Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L30-L33

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.wordPairing_columnExtension (x : Word F (A × B)) (b : B) (c : Word F A) :
    wordPairing x (columnExtension b c) = wordPairing (columnRestriction b x) c := by sorry
