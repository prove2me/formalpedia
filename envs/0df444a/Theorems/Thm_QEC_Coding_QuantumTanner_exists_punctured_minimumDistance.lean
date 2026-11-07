-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_punctured_minimumDistance
-- name    : QEC.Coding.QuantumTanner.exists_punctured_minimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:49:36.416529+00:00
-- url     : https://prove2.me/theorems/9bd757ef-64df-4d2e-9442-c37eda193e08
-- title:
--   Quantum Tanner: exists punctured minimum Distance
-- statement:
--   Fewer deletions than the actual distance preserve a nonzero word and hence
--   an attained punctured minimum. No punctured-distance witness is postulated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L193-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L193-L210

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_punctured_minimumDistance [DecidableEq F]
    (C : LinearCode F A) (d : Nat) (hC : MinimumDistance C d)
    (removed : Finset A) (hRemoved : removed.card < d) :
    ∃ d', MinimumDistance (puncturedCode C removed) d' ∧ d - removed.card ≤ d' := by sorry
