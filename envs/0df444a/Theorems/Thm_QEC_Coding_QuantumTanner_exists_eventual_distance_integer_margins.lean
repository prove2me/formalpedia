-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_integer_margins
-- name    : QEC.Coding.QuantumTanner.exists_eventual_distance_integer_margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:48.887745+00:00
-- url     : https://prove2.me/theorems/10ae957a-06dd-4537-af11-e989adbcfe2c
-- title:
--   Quantum Tanner: exists eventual distance integer margins
-- statement:
--   Integer versions of the source's robustness and final descent margins.
--   The actual floor punctures and ceiling-based line error are used throughout.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L158-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L158-L265

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter

theorem QEC.Coding.QuantumTanner.exists_eventual_distance_integer_margins
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      let d := Nat.ceil (delta * Delta)
      let e := distanceLineError delta epsilon Delta
      let p := Nat.floor ((Delta : ℝ) ^ gamma)
      let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
      2 ≤ Delta ∧ 0 < distanceNormalCutoff epsilon Delta ∧
      distanceNormalCutoff epsilon Delta - 1 ≤ w ∧
      p ≤ Delta ∧ p < d ∧ e < d ∧
      2 * w ≤ (d - p) * (d - p) ∧ 2 * Delta * e ≤ w ∧
      ((6 * Delta * e + 4 * Delta * p : Nat) : ℝ) <
        (d - e : Nat) * (delta ^ 2 * Delta / 256) ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ) := by sorry
