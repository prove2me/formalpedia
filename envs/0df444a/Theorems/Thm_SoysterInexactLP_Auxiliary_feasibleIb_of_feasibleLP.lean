-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_feasibleIb_of_feasibleLP
-- name    : SoysterInexactLP.Auxiliary.feasibleIb_of_feasibleLP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:25.346147+00:00
-- url     : https://prove2.me/theorems/34a71a28-258a-4779-8c13-fda820b3d677
-- title:
--   Feasible for LP(Ā) implies feasible for (Ib)
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets with $\delta^*(e_i\mid K_j)<\infty$ for all $i,j$, let $b\in\mathbb R^m$ and let $\bar A$ have entries $\bar a_{ij}=\delta^*(e_i\mid K_j)$. If $x$ satisfies
--   $$\bar A x\le b,\qquad x\ge0,$$
--   then $x$ is feasible for (Ib): $x_1K_1+\cdots+x_nK_n\subseteq\{y\mid y\le b\}$.
--
--   This is the first half of the THEOREM.
--
--   **Formalization Note** Convexity is a standing assumption and unused.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), proof of THEOREM, first paragraph

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem feasibleIb_of_feasibleLP {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : FeasibleLP (Abar K) b x) :
    FeasibleIb K b x := by sorry

end SoysterInexactLP.Auxiliary
