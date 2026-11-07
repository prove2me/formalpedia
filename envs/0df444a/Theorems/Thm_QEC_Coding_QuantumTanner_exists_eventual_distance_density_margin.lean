-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_density_margin
-- name    : QEC.Coding.QuantumTanner.exists_eventual_distance_density_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:15.70373+00:00
-- url     : https://prove2.me/theorems/b9d062ed-0510-4ceb-b928-2e3ae0f8289e
-- title:
--   Quantum Tanner: exists eventual distance density margin
-- statement:
--   The union-graph density loss is also sublinear. This statement does not
--   restrict `delta` to be at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L269-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L269-L289

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter

theorem QEC.Coding.QuantumTanner.exists_eventual_distance_density_margin
    (delta epsilon : ℝ) (hDeltaDistance : 0 < delta) (hEpsilon : 0 < epsilon) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      2 ≤ Delta ∧
      (distanceLineError delta epsilon Delta : ℝ) +
        (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2 := by sorry
