-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasMinimumDistanceAtLeast_punctured
-- name    : QEC.Coding.QuantumTanner.hasMinimumDistanceAtLeast_punctured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:49:25.089798+00:00
-- url     : https://prove2.me/theorems/d18ea038-5a3a-441e-ad42-78f38d2629ea
-- title:
--   Quantum Tanner: has Minimum Distance At Least punctured
-- statement:
--   The actual punctured code retains the expected minimum-distance lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L178-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L178-L189

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hasMinimumDistanceAtLeast_punctured [DecidableEq F]
    (C : LinearCode F A) (d : Nat) (hC : HasMinimumDistanceAtLeast C d)
    (removed : Finset A) :
    HasMinimumDistanceAtLeast (puncturedCode C removed) (d - removed.card) := by sorry
