-- Prove2me | Theorems.Thm_SemidefiniteProgramming_kkt_of_posDef
-- name    : SemidefiniteProgramming.kkt_of_posDef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:02.724963+00:00
-- url     : https://prove2.me/theorems/36816595-e569-484c-a0be-ecb43d7ad654
-- title:
--   KKT conditions at a maximizer of a semidefinite-constrained linear program
-- statement:
--   Fix $N, m \in \mathbb{N}$, a matrix $A_0 \in \mathbb{R}^{N \times N}$, symmetric matrices
--   $A_1, \dots, A_m \in \mathbb{R}^{N \times N}$, a predicate $I$ on indices marking which
--   constraints are inequalities, and a cost vector $u \in \mathbb{R}^{m}$. Consider maximizing
--   $u \cdot \gamma$ over $\gamma \in \mathbb{R}^{m}$ subject to
--
--   $$
--   A_0 + \sum_{i} \gamma_i A_i \succeq 0, \qquad \gamma_i \ge 0 \ \text{ for } i \in I .
--   $$
--
--   Let $\hat\gamma$ be feasible, maximizing, and strictly feasible in the semidefinite constraint:
--   $A_0 + \sum_i \hat\gamma_i A_i \succ 0$. Then the cost vector satisfies the first-order
--   conditions
--
--   $$
--   u_i \le 0 \ (i \in I), \qquad u_i = 0 \ (i \notin I), \qquad
--   \hat\gamma_i \, u_i = 0 \ \text{ for every } i .
--   $$
--
--   Strict feasibility of the semidefinite constraint at the optimum means it is inactive there, so
--   only the sign constraints can bind, and complementary slackness pins the cost on every index
--   where $\hat\gamma$ is strictly positive. This is the step that extracts usable sign information
--   from an optimality assumption, and it is what a worst-case analysis needs when it has to show
--   that an optimal multiplier vector is supported where the problem allows.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2745-2867 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix

theorem SemidefiniteProgramming.kkt_of_posDef {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i, (A i).IsSymm)
    (I : Fin m → Prop) (u γh : Fin m → ℝ) (hγI : ∀ i, I i → 0 ≤ γh i)
    (hPD : (A₀ + ∑ i, γh i • A i).PosDef)
    (hmax : ∀ γ : Fin m → ℝ, (A₀ + ∑ i, γ i • A i).PosSemidef → (∀ i, I i → 0 ≤ γ i) →
      u ⬝ᵥ γ ≤ u ⬝ᵥ γh) :
    ∀ i, (I i → u i ≤ 0) ∧ (¬ I i → u i = 0) ∧ γh i * u i = 0 := by sorry
