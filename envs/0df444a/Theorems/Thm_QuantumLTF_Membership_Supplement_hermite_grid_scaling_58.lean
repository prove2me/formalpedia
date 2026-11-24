-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_grid_scaling_58
-- name    : QuantumLTF.Membership.Supplement.hermite_grid_scaling_58
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:51:25.60573+00:00
-- url     : https://prove2.me/theorems/e6ddb895-cb74-4899-a5b5-7aad90b6ad7b
-- title:
--   The Theorem 5.8 grid scale dominates all five Hermite-preparation size requirements
-- statement:
--   Fix A>0 and C≥0. There is a universal coefficient B, depending only on A and C, such that for all real n,K≥1 the choice η=A/K^(1/4), D=2K+1 makes each of the five lower-bound expressions for M in Theorem 5.2 at most B n^(13/4) K^(49/16). Thus the grid scale used in Theorem 5.8 simultaneously controls the two polynomial discretization bounds, the inverse-fourth-power error bound, the logarithmic tail bound, and the quantum Hermite-transform size bound. Formalization Note. This result handles the five numerical lower bounds on M; the separate condition D>log(4n/η) and the gate-efficient construction remain separate proof obligations.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 5.

import Mathlib

theorem QuantumLTF.Membership.Supplement.hermite_grid_scaling_58 (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ n K : ℝ, 1 ≤ n → 1 ≤ K →
      let η := A / K^(1/4:ℝ)
      let D := 2*K+1
      let S := n^(13/4:ℝ) * K^(49/16:ℝ)
      64*n^2*(D+1) ≤ B*S ∧
      20736*n^2*(D+1)/η^2 ≤ B*S ∧
      165888*n/η^4 ≤ B*S ∧
      4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ B*S ∧
      C * D^(9/4:ℝ) * (4*n/η)^(13/4:ℝ) ≤ B*S := by sorry
