-- Prove2me | Theorems.Thm_Polyhedral_lp_min_attained
-- name    : Polyhedral.lp_min_attained
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:26:18.598169+00:00
-- url     : https://prove2.me/theorems/7f799748-1c9e-4733-914f-302de2de257e
-- title:
--   A feasible linear program in standard form bounded below attains its minimum
-- statement:
--   **Attainment for a linear program in standard form.** Let $W \in \mathbb{R}^{m\times n}$, $q \in \mathbb{R}^n$ and $d \in \mathbb{R}^m$, and consider
--
--   $$\min \; q^{\mathsf T} y \qquad \text{subject to}\qquad W y = d,\ \ y \ge 0 .$$
--
--   If the feasible set is nonempty and the objective is bounded below on it, then the infimum is attained: some feasible $y_0$ satisfies $q^{\mathsf T} y_0 \le q^{\mathsf T} y$ for every feasible $y$.
--
--   Unlike a continuous function on a compact set, a linear function on an unbounded polyhedron has no a priori reason to attain its infimum; that it does is a genuinely polyhedral phenomenon, and it is what allows optimal bases, complementary slackness and the simplex method to be discussed at all. The proof here goes through the closedness of the finitely generated cone spanned by the augmented columns $(q_j, W_{\cdot j}) \in \mathbb{R}^{1+m}$.
--
--   **Formalization note.** Boundedness below is stated as the existence of a single $\beta$ below all feasible objective values, and optimality of $y_0$ as a pointwise inequality against all feasible $y$; no separate notion of "optimal value" is introduced.
-- source:
--   D. Bertsimas and J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Chapter 2 (Theorem 2.8) and Chapter 4

import Mathlib

open Matrix

theorem Polyhedral.lp_min_attained {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ)
    (d : Fin m → ℝ)
    (hfeas : ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ W.mulVec y = d)
    (hbdd : ∃ beta : ℝ, ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → W.mulVec y = d → beta ≤ q ⬝ᵥ y) :
    ∃ y0 : Fin n → ℝ, (∀ j, 0 ≤ y0 j) ∧ W.mulVec y0 = d ∧
      ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → W.mulVec y = d → q ⬝ᵥ y0 ≤ q ⬝ᵥ y := by sorry
