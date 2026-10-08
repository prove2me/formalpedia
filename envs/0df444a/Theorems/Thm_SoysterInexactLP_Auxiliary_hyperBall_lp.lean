-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_hyperBall_lp
-- name    : SoysterInexactLP.Auxiliary.hyperBall_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:32.297033+00:00
-- url     : https://prove2.me/theorems/f9b82c62-130f-471c-8441-c0eda784a54a
-- title:
--   Inexact LP with hypersphere uncertainty is the LP with columns aⱼ + ρⱼ·e
-- statement:
--   Let $A_0=(a_1,\dots,a_n)$ be an $m\times n$ matrix, $\rho_1,\dots,\rho_n\ge0$, $b\in\mathbb R^m$, and let $K_j$ be the Euclidean ball of radius $\rho_j$ around $a_j$. Then $x$ is feasible for (Ib) with these activity sets if and only if
--   $$x_1(a_1+\rho_1 e)+x_2(a_2+\rho_2 e)+\cdots+x_n(a_n+\rho_n e)\le b\qquad\text{and}\qquad x_j\ge0\ \forall j,$$
--   where $e$ is the vector of all ones. Consequently, for every objective $c$, the optimal solutions of (Ib) are exactly the optimal solutions of
--   $$\max c\cdot x\quad\text{s.t.}\quad x_1(a_1+\rho_1 e)+\cdots+x_n(a_n+\rho_n e)\le b,\ x_j\ge0.$$
--
--   This is the paper's application: a linear program whose activity vectors are known only up to a ball of radius $\rho_j$ is solved by an ordinary linear program with inflated columns.
--
--   **Formalization Note** "Optimal solution" means a feasible point attaining the maximum of $c\cdot x$ over the feasible set. The norm is Euclidean and the radii are nonnegative.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1157 (PDF p. 5), §Inexact Linear Programming, last display

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem hyperBall_lp {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (b : Fin m → ℝ) :
    {x | FeasibleIb (hyperBall A₀ ρ) b x} =
        {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j • (fun i => A₀ i j + ρ j) ≤ b} ∧
      ∀ c x : Fin n → ℝ,
        IsOptimal (FeasibleIb (hyperBall A₀ ρ) b) c x ↔
          IsOptimal (fun y => (∀ j, 0 ≤ y j) ∧ ∑ j, y j • (fun i => A₀ i j + ρ j) ≤ b) c x := by sorry

end SoysterInexactLP.Auxiliary
