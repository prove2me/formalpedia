-- Prove2me | Theorems.Thm_Polyhedral_lp_strong_duality
-- name    : Polyhedral.lp_strong_duality
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:26:14.708716+00:00
-- url     : https://prove2.me/theorems/b48e1a23-fea8-4422-967e-7d4974d10b6f
-- title:
--   Strong duality and complementary slackness for a standard-form linear program
-- statement:
--   **Strong duality and complementary slackness for a linear program in standard form.** Let $M \in \mathbb{R}^{m \times n}$, $d \in \mathbb{R}^n$, $g \in \mathbb{R}^m$, and suppose $u_0$ is optimal for
--
--   $$\min \; d^{\mathsf T} u \qquad \text{subject to}\qquad M u = g,\ \ u \ge 0 .$$
--
--   Then there is a dual vector $p \in \mathbb{R}^m$ with
--
--   $$M^{\mathsf T} p \le d, \qquad g^{\mathsf T} p = d^{\mathsf T} u_0, \qquad (u_0)_j\big(d_j - (M^{\mathsf T}p)_j\big) = 0 \ \ \text{for every } j .$$
--
--   The first condition is feasibility for the dual program $\max\{g^{\mathsf T}p : M^{\mathsf T}p \le d\}$, the second says the duality gap vanishes, and the third is complementary slackness: a variable that is positive in the primal forces its dual constraint to be tight.
--
--   This is the statement on which the optimality conditions of linear programming rest, and through which multipliers are extracted for problems, such as two-stage stochastic programs, whose deterministic equivalent is a linear program. The proof applies Gale's theorem of the alternative to the system $M^{\mathsf T}p \le d$, $g^{\mathsf T}p \ge d^{\mathsf T}u_0$: an alternative certificate would produce either a strictly better feasible point or a feasible direction of strictly negative cost, contradicting optimality of $u_0$.
--
--   **Formalization note.** Optimality of $u_0$ is given as a hypothesis in pointwise form (it is a minimizer over the feasible set), so no notion of optimal value is needed; attainment of the primal minimum is therefore assumed rather than derived here.
-- source:
--   D. Bertsimas and J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 4.3 (Theorem 4.4) and Section 4.5

import Mathlib

open Matrix

theorem Polyhedral.lp_strong_duality {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (g : Fin m → ℝ) (u0 : Fin n → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hMu0 : M.mulVec u0 = g)
    (hopt : ∀ u : Fin n → ℝ, (∀ j, 0 ≤ u j) → M.mulVec u = g → d ⬝ᵥ u0 ≤ d ⬝ᵥ u) :
    ∃ p : Fin m → ℝ, (∀ j, Mᵀ.mulVec p j ≤ d j) ∧ g ⬝ᵥ p = d ⬝ᵥ u0 ∧
      ∀ j, u0 j * (d j - Mᵀ.mulVec p j) = 0 := by sorry
