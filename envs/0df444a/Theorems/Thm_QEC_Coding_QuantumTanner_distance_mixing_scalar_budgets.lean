-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_distance_mixing_scalar_budgets
-- name    : QEC.Coding.QuantumTanner.distance_mixing_scalar_budgets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:12.37387+00:00
-- url     : https://prove2.me/theorems/fb89f5b3-4798-47bf-987f-d335b3d331ae
-- title:
--   Quantum Tanner: distance mixing scalar budgets
-- statement:
--   Exact scalar mixing budgets used in the source distance argument.
--   `s` is the actual active-vertex count, and `n` the actual group cardinality.
--   No graph or spectral conclusion is encoded in these arithmetic hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L294-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean#L294-L430

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter

theorem QEC.Coding.QuantumTanner.distance_mixing_scalar_budgets
    (delta epsilon : ℝ) (Delta s n p : Nat)
    (hDelta : 2 ≤ Delta) (hDeltaDistance : 0 < delta)
    (hSmall : (s : ℝ) ≤ n / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)))
    (hError : distanceLineError delta epsilon Delta < Nat.ceil (delta * Delta))
    (hDensity : (distanceLineError delta epsilon Delta : ℝ) +
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2)
    (hFractionHalf : 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2)
    (hPuncture : 40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ)) :
    let normal := (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)
    let fraction := 64 / (Delta : ℝ) ^ (1 - 2 * epsilon)
    let gap := delta * Delta / 2
    let ratio := 64 / (delta ^ 2 * Delta)
    let threshold := delta ^ 2 * Delta / 256
    let uniform := 32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)
    2 * ((Delta * Delta : Nat) : ℝ) * s ≤ normal * n ∧
    4 * (4 * (Delta : ℝ)) ^ 2 ≤ fraction * normal ^ 2 ∧
    ((Delta + Delta : Nat) : ℝ) * s + gap * n ≤
      ((Nat.ceil (delta * Delta) - distanceLineError delta epsilon Delta : Nat) : ℝ) * n ∧
    (4 * Real.sqrt (Delta : ℝ)) ^ 2 ≤ ratio * gap ^ 2 ∧
    2 * threshold * ratio ≤ 1 - fraction ∧
    ((Delta + Delta : Nat) : ℝ) * (fraction * s) ≤ uniform * n ∧
    (uniform + 4 * Real.sqrt (Delta : ℝ) *
      Real.sqrt (fraction * (2 * ((Delta + Delta : Nat) : ℝ)))) *
      ((Delta + Delta : Nat) : ℝ) ≤ (p : ℝ) * threshold := by sorry
