-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_wordPairing_rowExtension
-- name    : QEC.Coding.QuantumTanner.wordPairing_rowExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:27.038652+00:00
-- url     : https://prove2.me/theorems/04086350-7d70-404d-9398-ba1d30b24f0e
-- title:
--   Quantum Tanner: word Pairing row Extension
-- statement:
--   The Quantum Tanner construction uses the word Pairing row Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L35-L38

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.wordPairing_rowExtension (x : Word F (A × B)) (a : A) (r : Word F B) :
    wordPairing x (rowExtension a r) = wordPairing (rowRestriction a x) r := by sorry
