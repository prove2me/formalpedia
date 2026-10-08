-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_theorem_lp_feasible_iff
-- name    : SoysterInexactLP.Auxiliary.theorem_lp_feasible_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:54.901989+00:00
-- url     : https://prove2.me/theorems/94236870-c7af-4c20-a073-870ca27a76d8
-- title:
--   THEOREM — (Ib) and LP(Ā) have the same feasible solutions and the same optimal solutions
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex activity sets with
--   $$\delta^*(e_i\mid K_j)=\sup_{a_j\in K_j}a_{ij}<\infty\qquad\text{for all } i,j,$$
--   let $b\in\mathbb R^m$, and let $\bar A$ be the $m\times n$ matrix with entries $\bar a_{ij}=\delta^*(e_i\mid K_j)$. Then
--
--   1. $x\in\mathbb R^n$ is feasible for (Ib), i.e. $x\ge0$ and $x_1K_1+\cdots+x_nK_n\subseteq\{y\mid y\le b\}$, if and only if it is feasible for LP$(\bar A)$, i.e. $\bar Ax\le b$ and $x\ge0$;
--   2. hence, for every $c\in\mathbb R^n$, $x$ is an optimal solution of $\sup c\cdot x$ over (Ib) if and only if it is an optimal solution of $\max c\cdot x$ over LP$(\bar A)$.
--
--   This reduces the convex program (Ib), whose constraint is the inclusion of a Minkowski sum of uncertain activity sets in a half-space intersection, to an ordinary linear program; it is the origin of the "worst-case column" robust counterpart in robust linear optimization.
--
--   **Formalization Note** An optimal solution is a feasible point attaining the maximum of $c\cdot x$; the paper does not discuss attainment, and the equality of the feasible sets makes the two problems have the same suprema as well. Convexity of the $K_j$ is the paper's standing assumption and is not needed for this statement.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), THEOREM

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem theorem_lp_feasible_iff {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤) (b : Fin m → ℝ) :
    {x | FeasibleIb K b x} = {x | FeasibleLP (Abar K) b x} ∧
      ∀ c x : Fin n → ℝ,
        IsOptimal (FeasibleIb K b) c x ↔ IsOptimal (FeasibleLP (Abar K) b) c x := by sorry

end SoysterInexactLP.Auxiliary
