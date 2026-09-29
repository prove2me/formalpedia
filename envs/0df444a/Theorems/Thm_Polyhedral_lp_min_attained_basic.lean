-- Prove2me | Theorems.Thm_Polyhedral_lp_min_attained_basic
-- name    : Polyhedral.lp_min_attained_basic
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-28T00:36:04.662139+00:00
-- url     : https://prove2.me/theorems/348c3fc2-9cf2-4105-bd99-d11498852ce1
-- title:
--   A bounded feasible standard-form LP attains its minimum at a basic feasible solution
-- statement:
--   **Existence of an optimal basic feasible solution.** Consider the linear program in standard form
--
--   $$\min\ q^{\mathsf T} y \qquad \text{subject to}\qquad W y = d,\ \ y \ge 0 .$$
--
--   If it is feasible and its objective is bounded below on the feasible set, then the minimum is attained at a point $y_0$ whose *support columns are linearly independent*: the columns $W_{\cdot j}$ with $(y_0)_j \ne 0$ form a linearly independent family.
--
--   This is the fundamental structural theorem of linear programming — the statement that optimisation may be restricted to basic feasible solutions, of which there are only finitely many. It underlies the simplex method, the finiteness of the set of candidate optima, and uniform bounds on optimal solutions as the right-hand side varies.
--
--   **Formalization note.** A basic feasible solution is described here directly by the linear independence of its support columns, `LinearIndepOn \u211d (fun j => fun i => W i j) {j | y0 j \u2260 0}`, rather than through a choice of basis matrix; this avoids assuming that $W$ has full row rank. Optimality is stated pointwise against all feasible points, and boundedness below as the existence of a single real lower bound for the objective on the feasible set.
-- source:
--   D. Bertsimas and J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.6, Theorem 2.8

import Mathlib

open Matrix

theorem Polyhedral.lp_min_attained_basic {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (d : Fin m → ℝ)
    (hfeas : ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ W.mulVec y = d)
    (hbdd : ∃ beta : ℝ, ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → W.mulVec y = d →
      beta ≤ q ⬝ᵥ y) :
    ∃ y0 : Fin n → ℝ, (∀ j, 0 ≤ y0 j) ∧ W.mulVec y0 = d ∧
      (∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → W.mulVec y = d → q ⬝ᵥ y0 ≤ q ⬝ᵥ y) ∧
      LinearIndepOn ℝ (fun j => (fun i => W i j)) {j | y0 j ≠ 0} := by sorry
