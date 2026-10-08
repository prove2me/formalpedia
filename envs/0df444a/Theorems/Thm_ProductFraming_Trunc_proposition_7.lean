-- Prove2me | Theorems.Thm_ProductFraming_Trunc_proposition_7
-- name    : ProductFraming.Trunc.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:42.561995+00:00
-- url     : https://prove2.me/theorems/b43c405a-0839-4b03-ba03-970af52e6374
-- title:
--   Proposition 7 — at an optimum of (10), $h(x)=h(y)$ for $x=y,\dots,m-1$
-- statement:
--   Let $m\ge 1$ and let $(U,\Lambda)$ be an optimal solution of program (10) with $\Lambda(x)>0$ for all $x\in[m]$, failure rate $h(x)=\lambda(x)/\Lambda(x)$, $\lambda(x)=\Lambda(x)-\Lambda(x+1)$ and $\Lambda(m+1)=0$. If $y$ is the largest maximizer of $x\mapsto U(x)\Lambda(x)$ on $[m]$, then
--
--   $$h(x)=h(y)\qquad\text{for all }x=y,\dots,m-1.$$
--
--   So beyond $y$ the optimal page-count law is a truncated geometric distribution, which is what makes the final computation of $\mathbf E[X\mid X\ge y]$ in the proof of Theorem 4 possible.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.4, p. 41, Proposition 7 (with the A.4 preamble, p. 39)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Program10
open Finset

namespace ProductFraming.Trunc

theorem proposition_7 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) (h_opt : IsOptimal10 m hm U L)
    (h_pos : ∀ x ∈ Icc 1 m, 0 < L x) (y : ℕ)
    (hy : IsLargestMaximizer m (fun x => U x * L x) y) :
    ∀ x : ℕ, y ≤ x → x + 1 ≤ m → hazard m L x = hazard m L y := by sorry

end ProductFraming.Trunc
