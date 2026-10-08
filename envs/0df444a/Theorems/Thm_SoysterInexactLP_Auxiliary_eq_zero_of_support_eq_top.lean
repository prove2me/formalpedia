-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_eq_zero_of_support_eq_top
-- name    : SoysterInexactLP.Auxiliary.eq_zero_of_support_eq_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:21.210407+00:00
-- url     : https://prove2.me/theorems/1960ff5c-e508-482d-8612-93c8516baf15
-- title:
--   An infinite support functional δ*(eᵢ|Kⱼ) = ∞ forces xⱼ = 0 in (Ib)
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets and $b\in\mathbb R^m$. Suppose $x$ is feasible for (Ib), i.e. $x\ge0$ and $\sum_{j=1}^n x_jK_j\subseteq K(b)=\{y\mid y\le b\}$. If for some row $i$ and column $j$
--   $$\delta^*(e_i\mid K_j)=\sup_{a_j\in K_j}a_{ij}=+\infty,$$
--   then $x_j=0$.
--
--   This justifies deleting from (Ib) every activity set whose support functional is infinite in some coordinate direction, so that the auxiliary linear program can be formed with finite entries.
--
--   **Formalization Note** Nonemptiness of all the $K_l$ is needed (with an empty $K_l$ the Minkowski sum is empty and every $x\ge0$ is feasible); convexity is the paper's standing assumption and is not needed.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1155 (PDF p. 3), paragraph defining āⱼ

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem eq_zero_of_support_eq_top {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j)) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : FeasibleIb K b x) (i : Fin m) (j : Fin n)
    (htop : supportFun (K j) (Pi.single i 1) = ⊤) :
    x j = 0 := by sorry

end SoysterInexactLP.Auxiliary
