-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_puncture_loss_le
-- name    : QEC.Coding.QuantumTanner.hammingWeight_puncture_loss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:30:44.066289+00:00
-- url     : https://prove2.me/theorems/af2e4eea-b307-4d54-b232-f8d6a9d59665
-- title:
--   Quantum Tanner: hamming Weight puncture loss le
-- statement:
--   Deleting coordinates loses at most their cardinality in Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L154-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L154-L175

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_puncture_loss_le [DecidableEq F]
    (removed : Finset A) (x : Word F A) :
    HammingWeight x ≤ HammingWeight (punctureMap removed x) + removed.card := by sorry
