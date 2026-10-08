-- Prove2me | Theorems.Thm_ProductFraming_Trunc_proposition_6
-- name    : ProductFraming.Trunc.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:43.342985+00:00
-- url     : https://prove2.me/theorems/f5e4be98-8dc1-4f63-b8e1-84ac0ee72c63
-- title:
--   Proposition 6 — at an optimum of (10), $U(x)\Lambda(x)=U(y)\Lambda(y)$ for $x=1,\dots,y$
-- statement:
--   Let $m\ge 1$ and let $(U,\Lambda)$ be an optimal solution of program (10) with $\Lambda(x)>0$ for all $x\in[m]$. If $y$ is the largest maximizer of $x\mapsto U(x)\Lambda(x)$ on $[m]$, then the objective is attained at every page up to $y$:
--
--   $$U(x)\Lambda(x)=U(y)\Lambda(y)\qquad\text{for all }x=1,\dots,y.$$
--
--   With Proposition 5 this determines $U$ on all of $[m]$ in terms of $U(y)\Lambda(y)$ and $\Lambda$.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.4, p. 41, Proposition 6 (with the A.4 preamble, p. 39)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Program10
open Finset

namespace ProductFraming.Trunc

theorem proposition_6 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) (h_opt : IsOptimal10 m hm U L)
    (h_pos : ∀ x ∈ Icc 1 m, 0 < L x) (y : ℕ)
    (hy : IsLargestMaximizer m (fun x => U x * L x) y) :
    ∀ x ∈ Icc 1 y, U x * L x = U y * L y := by sorry

end ProductFraming.Trunc
