-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_feasibleLP_of_feasibleIb
-- name    : SoysterInexactLP.Auxiliary.feasibleLP_of_feasibleIb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:44.910468+00:00
-- url     : https://prove2.me/theorems/2ee68b1e-ca9f-4bc2-b304-cc633bd94bad
-- title:
--   Feasible for (Ib) implies x₁ sup aᵢ₁ + ⋯ + xₙ sup aᵢₙ ≦ bᵢ, i.e. feasible for LP(Ā)
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets with $\delta^*(e_i\mid K_j)<\infty$ for all $i,j$, and let $b\in\mathbb R^m$. If $x$ is feasible for (Ib), then for every $i=1,\dots,m$
--   $$x_1\sup_{a_1\in K_1}a_{i1}+\cdots+x_n\sup_{a_n\in K_n}a_{in}\le b_i,$$
--   and consequently $x$ is feasible for LP$(\bar A)$: $\bar Ax\le b$ and $x\ge0$.
--
--   This is the second half of the THEOREM.
--
--   **Formalization Note** The suprema are $\delta^*(e_i\mid K_j)$ converted to real numbers, exact under the nonemptiness and finiteness hypotheses. Convexity is a standing assumption and unused.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), proof of THEOREM, second paragraph

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem feasibleLP_of_feasibleIb {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : FeasibleIb K b x) :
    (∀ i, ∑ j, x j * (supportFun (K j) (Pi.single i 1)).toReal ≤ b i) ∧
      FeasibleLP (Abar K) b x := by sorry

end SoysterInexactLP.Auxiliary
