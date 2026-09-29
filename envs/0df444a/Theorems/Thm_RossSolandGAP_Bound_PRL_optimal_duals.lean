-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_PRL_optimal_duals
-- name    : RossSolandGAP.Bound.PRL_optimal_duals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:13:16.345275+00:00
-- url     : https://prove2.me/theorems/4cbf37e7-b57f-46a1-a468-d1b94ce0d7fc
-- title:
--   §2, pp. 95–96 — the optimal dual multipliers of (PR_L) are exactly c_1j ≤ λ_j ≤ c_2j
-- statement:
--   Let $m\ge2$ and let $j\mapsto i_j$ be a cheapest-agent selection, so $c_{1j}=c_{i_jj}$ is the smallest and $c_{2j}$ the second smallest of $c_{1j},\dots,c_{mj}$. Consider the bounded-variable linear program
--
--   $$
--   \text{(PR}_L)\qquad\min\ \sum_{i\in I}\sum_{j\in J}c_{ij}x_{ij}\quad\text{s.t.}\quad\sum_{i\in I}x_{ij}=1\ (j\in J),\quad 0\le x_{ij}\le1,
--   $$
--
--   and its linear-programming dual, with a free multiplier $\lambda_j$ for each equation and a multiplier $u_{ij}\ge0$ for each upper bound $x_{ij}\le1$:
--
--   $$
--   \max\ \sum_{j\in J}\lambda_j-\sum_{i\in I}\sum_{j\in J}u_{ij}\quad\text{s.t.}\quad\lambda_j-u_{ij}\le c_{ij},\ u_{ij}\ge0 .
--   $$
--
--   Then:
--
--   1. the (PR) solution ($x_{i_jj}=1$, other entries $0$) is optimal for (PR$_L$), with value $Z=\sum_jc_{1j}$;
--   2. a vector $\lambda$ is part of an optimal dual solution $(\lambda,u)$ if and only if
--   $$
--   c_{1j}\le\lambda_j\le c_{2j}\qquad\text{for all }j\in J.
--   $$
--
--   This is the paper's remark that "each optimal dual multiplier $\lambda_j$ for (PR$_L$) lies anywhere in the range $c_{1j}\le\lambda_j\le c_{2j}$", so optimal multipliers are very easy to compute, and $\lambda=c_2$ is the largest of them.
--
--   **Formalization Note** "Lies anywhere in the range" is read as: the set of optimal $\lambda$ is exactly the box $\prod_j[c_{1j},c_{2j}]$. The claim depends on the upper bounds $x_{ij}\le1$ carrying dual multipliers; without them only $\lambda_j\le c_{1j}$ is dual feasible. The dual is written out explicitly; no LP duality theorem is assumed. Agents and tasks are 0-based.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, pp. 95-96, §2, (PR_L) and the sentence 'It is particularly important to note that each optimal dual multiplier ...'

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem PRL_optimal_duals {m n : ℕ} (hm : 1 < m) (c : Fin m → Fin n → ℝ)
    (a : Fin n → Fin m) (ha : IsCheapest c a) :
    (FeasiblePRL (xPR a) ∧ cost c (xPR a) = Z c a ∧
      ∀ x, FeasiblePRL x → Z c a ≤ cost c x) ∧
    ∀ lam : Fin n → ℝ, (∃ u, IsOptDualPRL c lam u) ↔
      ∀ j, c (a j) j ≤ lam j ∧ lam j ≤ c2 hm c a j := by sorry

end RossSolandGAP.Bound
