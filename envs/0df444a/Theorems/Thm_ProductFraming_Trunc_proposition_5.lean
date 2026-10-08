-- Prove2me | Theorems.Thm_ProductFraming_Trunc_proposition_5
-- name    : ProductFraming.Trunc.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:48.932753+00:00
-- url     : https://prove2.me/theorems/2481f65d-ab09-4869-b06a-097ef8bb38bd
-- title:
--   Proposition 5 — at an optimum of (10), $U(x)/x=U(y)/y$ for $x=y,\dots,m$
-- statement:
--   Let $m\ge 1$ and let $(U,\Lambda)$ be an optimal solution of program (10) with $\Lambda(x)>0$ for all $x\in[m]$. Let $y$ be the largest maximizer of $x\mapsto U(x)\Lambda(x)$ on $[m]$. Then
--
--   $$\frac{U(x)}{x}=\frac{U(y)}{y}\qquad\text{for all }x=y,\dots,m.$$
--
--   So beyond the page $y$ where the objective is attained, the constraint $U(x)/x\ge U(x+1)/(x+1)$ is tight at every optimum.
--
--   **Formalization Note** The statement holds for every optimal solution with $\Lambda>0$ on $[m]$ (the A.4 preamble: "Let $(U,\Lambda)$ denote an optimal solution to (10)", with $\Lambda>0$ assumed without loss of generality).
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.4, p. 40, Proposition 5 (with the A.4 preamble, p. 39)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Program10
open Finset

namespace ProductFraming.Trunc

theorem proposition_5 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) (h_opt : IsOptimal10 m hm U L)
    (h_pos : ∀ x ∈ Icc 1 m, 0 < L x) (y : ℕ)
    (hy : IsLargestMaximizer m (fun x => U x * L x) y) :
    ∀ x ∈ Icc y m, U x / (x : ℝ) = U y / (y : ℝ) := by sorry

end ProductFraming.Trunc
