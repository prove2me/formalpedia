-- Prove2me | Theorems.Thm_VWZClique_weighted_nine
-- name    : VWZClique.weighted_nine
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:04:36.700205+00:00
-- url     : https://prove2.me/theorems/c04601f4-415d-4cfa-9b8b-b09cbfccefca
-- title:
--   Theorem 1.2 — Weighted nine-vertex pattern sums
-- statement:
--   Over every characteristic-zero field, all weighted nine-position homomorphism sums admit arithmetic programs of cost $n^{3\omega_F-\varepsilon+o(1)}$, for one absolute positive saving.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Theorem 1.2, equation (1), Section 3.4. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Weighted

open OAI.MatrixMultiplication.Arithmetic VWZClique

theorem VWZClique.weighted_nine :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type*) [Field F] [CharZero F],
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ∀ H : SimpleGraph V, computesWithin (weightedSum (F := F) (n := n) H)
          (C * (n : ℝ) ^ (3 * omega F - ε + η)) := by sorry
