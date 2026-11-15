-- Prove2me | Theorems.Thm_QuantumLTF_Membership_uniform_dyadic_window
-- name    : QuantumLTF.Membership.uniform_dyadic_window
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T04:32:29.067304+00:00
-- url     : https://prove2.me/theorems/39c19e0c-86a8-4e62-a33d-c9c7ad9be07f
-- title:
--   Uniform dyadic grid window probability
-- statement:
--   In every dimension at least two, a uniform signed dyadic grid with at most four plus the base-two logarithmic ceiling bits per coordinate has inner-product magnitude between 1/10 and 3 with probability at least 4/5 in every fixed unit direction.
-- source:
--   Small-ball and tail estimate underlying Lemma 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf
open QAlgorithms

theorem QuantumLTF.Membership.uniform_dyadic_window (n : ℕ) (hn : 2 ≤ n) :
    ∃ ℓ f : ℕ, f ≤ ℓ ∧ ℓ ≤ 4 + ⌈Real.logb 2 n⌉₊ ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        ((PMF.uniformOfFintype (Qubits (n * ℓ))).toOuterMeasure
          {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
            |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by sorry
