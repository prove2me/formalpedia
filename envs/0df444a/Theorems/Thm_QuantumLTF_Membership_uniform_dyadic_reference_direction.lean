-- Prove2me | Theorems.Thm_QuantumLTF_Membership_uniform_dyadic_reference_direction
-- name    : QuantumLTF.Membership.uniform_dyadic_reference_direction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T04:29:40.109659+00:00
-- url     : https://prove2.me/theorems/467b04b8-cf4f-4483-a251-ab12e74ebe3d
-- title:
--   Uniform dyadic sampler gives a well-conditioned reference direction
-- statement:
--   For each dimension at least two, one can choose a signed dyadic coordinate precision using O(log n) bits so that a uniformly random encoded grid vector has inner product magnitude between 1/10 and 3 with every fixed unit direction with probability at least 4/5.
-- source:
--   Statistical core of Lemma 3.1 in Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf
open QAlgorithms

theorem QuantumLTF.Membership.uniform_dyadic_reference_direction :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ ℓ f : ℕ, f ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log n ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ((PMF.uniformOfFintype (Qubits (n * ℓ))).toOuterMeasure
            {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
              |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by sorry
