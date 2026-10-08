-- Prove2me | Theorems.Thm_SPHardness_IntFeas_secondStage_solution
-- name    : SPHardness.IntFeas.secondStage_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:43.810355+00:00
-- url     : https://prove2.me/theorems/90b14ec8-0ec1-410b-beff-051b002ca364
-- title:
--   Proof of Theorem 4, p. 13 — the second stage of (11): optimal y is max{ξᵢ, 1 − ξᵢ} if Aξ ≤ b and 0 otherwise
-- statement:
--   Fix $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, a first-stage decision $x\in\mathbb R$ and a realization $\xi\in[0,1]^n$, and consider the second-stage problem of (11),
--   $$Q(x,\xi)=\inf\Big\{e^\top y : y\ge0,\ \lambda\ge0,\ x\ge e^\top y,\ y_i\ge\xi_i+(b-A\xi)^\top\lambda,\ y_i\ge(1-\xi_i)+(b-A\xi)^\top\lambda\ (i=1,\dots,n)\Big\}.$$
--   1. If $A\xi\le b$: the problem is feasible if and only if $\sum_i\max\{\xi_i,1-\xi_i\}\le x$; when it is feasible, $Q(x,\xi)=\sum_i\max\{\xi_i,1-\xi_i\}$, and every optimal solution $(y,\lambda)$ has $y_i=\max\{\xi_i,1-\xi_i\}$ for all $i$.
--   2. If $A\xi\not\le b$: the problem is feasible if and only if $x\ge0$; when it is feasible, $Q(x,\xi)=0$, and every optimal solution has $y=0$.
--
--   This is the explicit solution of the second stage on which the computation of the optimal decision $x^\star$ of (11) rests.
--
--   **Formalization Note.** "Optimal solution" is read as a feasible $(y,\lambda)$ with $e^\top y=Q(x,\xi)$. The page asserts only the form of $y$; $\lambda$ is not unique and nothing is claimed about it. The feasibility characterisations make explicit what the page's "if the second-stage problem is feasible" presupposes. The constraint block ranges over $i=1,\dots,n$ (the page prints $m$; see the definitions file).
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), §3, proof of Theorem 4, p. 13

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem secondStage_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : ℝ) (ξ : Fin n → ℝ) (hξ : ξ ∈ SPHardness.FixedRecourse.cube n) :
    (InPolytope A b ξ →
      (SecondStageSolvable A b x ξ ↔ ∑ i, max (ξ i) (1 - ξ i) ≤ x) ∧
      (SecondStageSolvable A b x ξ →
        secondStageValue A b x ξ = ∑ i, max (ξ i) (1 - ξ i)) ∧
      (∀ y lam, SecondStageFeasible A b x ξ y lam →
        ∑ i, y i = secondStageValue A b x ξ → ∀ i, y i = max (ξ i) (1 - ξ i))) ∧
    (¬ InPolytope A b ξ →
      (SecondStageSolvable A b x ξ ↔ 0 ≤ x) ∧
      (SecondStageSolvable A b x ξ → secondStageValue A b x ξ = 0) ∧
      (∀ y lam, SecondStageFeasible A b x ξ y lam →
        ∑ i, y i = secondStageValue A b x ξ → ∀ i, y i = 0)) := by sorry

end SPHardness.IntFeas
