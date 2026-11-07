-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_real_margins
-- name    : QEC.Coding.QuantumTanner.exists_eventual_distance_real_margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:24.879933+00:00
-- url     : https://prove2.me/theorems/e196b5fb-c44b-4975-a90b-cc91a27a7b5a
-- title:
--   Quantum Tanner: exists eventual distance real margins
-- statement:
--   The source exponent inequalities give all the real smallness margins
--   needed for exceptional sets, punctures, robustness and the final strict
--   weight decrease, including a genuine lower bound on the integer puncture budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L107-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L107-L154

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter

theorem QEC.Coding.QuantumTanner.exists_eventual_distance_real_margins
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      2 ≤ Delta ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta <
        min (delta / 4) (delta ^ 3 / 12288) * Delta ∧
      (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) <
        min (min (delta / 4) (delta ^ 3 / 8192)) 1 * Delta ∧
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2) <
        delta ^ 2 / 8 * (Delta : ℝ) ^ (2 : ℝ) ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
        (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) := by sorry
