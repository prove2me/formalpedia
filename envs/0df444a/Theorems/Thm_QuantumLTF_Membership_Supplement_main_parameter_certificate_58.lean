-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_main_parameter_certificate_58
-- name    : QuantumLTF.Membership.Supplement.main_parameter_certificate_58
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-24T20:17:07.524172+00:00
-- url     : https://prove2.me/theorems/f7ecc007-e17f-40c5-b1ff-2e3f58da4b86
-- title:
--   Theorem 5.8 — uniform error budget and complete numerical parameter admissibility
-- statement:
--   There is a universal A in (0,1/2) such that η=A K^(-1/4) is at most the required Hermite-preparation error budget sqrt(p_K)/192 for every hidden unit direction and K≥1. For every quantum-Hermite size coefficient C≥0 there are positive thresholds for c1,c2 such that all larger c1,c2, with K=ceil(c1 n/ε²) and q=ceil(log₂(c2 n^(13/4) K^(49/16))), satisfy every numerical hypothesis of Theorem 5.2. This includes the error range, degree lower bound, logarithmic degree condition, and all five lower bounds on M=2^q. The same parameters also give K^(1/4)+3=O(n^(1/4)/sqrt(ε)) and n K^(1/4)+K=O(n^(5/4)/sqrt(ε)+n/ε²), with constants chosen before n,ε. Formalization Note. This is the numerical parameter certificate in the proof of Theorem 5.8. It does not assert or assume the existence of the remaining gate-efficient preparation, conversion, or tomography algorithms, and its leading gate bound does not include their polylogarithmic factors.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 5.5 and Eqs. (190)–(194), using the proved Hermite-band mass bound from Section 5.2.

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
open QuantumLTF.Membership.Supplement

theorem QuantumLTF.Membership.Supplement.main_parameter_certificate_58 :
    ∃ A : ℝ, 0 < A ∧ A < 1/2 ∧
      (∀ n K : ℕ, 1 ≤ K → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        A/(K:ℝ)^(1/4:ℝ) ≤ Real.sqrt (bandWeight w K)/192) ∧
      ∀ C : ℝ, 0 ≤ C →
      ∃ c1₀ c2₀ : ℝ, 0 < c1₀ ∧ 0 < c2₀ ∧
      ∀ c1 c2 : ℝ, c1₀ ≤ c1 → c2₀ ≤ c2 →
        ∃ R : ℝ, 0 < R ∧ ∀ n ε : ℝ, 1 ≤ n → 0 < ε → ε < 1/2 →
          let K : ℕ := ⌈c1*n/ε^2⌉₊
          let η := A/(K:ℝ)^(1/4:ℝ)
          let D := 2*(K:ℝ)+1
          let q : ℕ := ⌈Real.logb 2 (c2*n^(13/4:ℝ)*(K:ℝ)^(49/16:ℝ))⌉₊
          (2 ≤ D ∧ 0 < η ∧ η < 1/2 ∧ Real.log (4*n/η) < D ∧
            64*n^2*(D+1) ≤ (2:ℝ)^q ∧
            20736*n^2*(D+1)/η^2 ≤ (2:ℝ)^q ∧
            165888*n/η^4 ≤ (2:ℝ)^q ∧
            4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q ∧
            C*D^(9/4:ℝ)*(4*n/η)^(13/4:ℝ) ≤ (2:ℝ)^q) ∧
          (K:ℝ)^(1/4:ℝ)+3 ≤ R*n^(1/4:ℝ)/Real.sqrt ε ∧
          n*(K:ℝ)^(1/4:ℝ)+(K:ℝ) ≤ R*(n^(5/4:ℝ)/Real.sqrt ε+n/ε^2) := by sorry
