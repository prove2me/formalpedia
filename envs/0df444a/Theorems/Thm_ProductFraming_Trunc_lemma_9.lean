-- Prove2me | Theorems.Thm_ProductFraming_Trunc_lemma_9
-- name    : ProductFraming.Trunc.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:42.491472+00:00
-- url     : https://prove2.me/theorems/389349a8-f46e-4a34-89c4-7ffd414221ec
-- title:
--   Lemma 9 — at an optimum of (10), $y$ is also the largest maximizer of $g(x)=x\Lambda(x)$
-- statement:
--   Let $m\ge 1$ and let $(U,\Lambda)$ be an optimal solution of program (10) with $\Lambda(x)>0$ for all $x\in[m]$. If $y$ is the largest maximizer of $x\mapsto U(x)\Lambda(x)$ on $[m]$, then $y$ is also the largest maximizer of $g(x)=x\Lambda(x)$:
--
--   $$y=\operatorname{maxarg\,max}_{x\in[m]}x\Lambda(x).$$
--
--   Together with Lemma 8 this locates $y$ through the failure rate: $y=\min\{x\in[m]:h(x)>1/(x+1)\}$.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.4, pp. 40–41, Lemma 9 (with the A.4 preamble, p. 39)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Program10
open Finset

namespace ProductFraming.Trunc

theorem lemma_9 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) (h_opt : IsOptimal10 m hm U L)
    (h_pos : ∀ x ∈ Icc 1 m, 0 < L x) (y : ℕ)
    (hy : IsLargestMaximizer m (fun x => U x * L x) y) :
    IsLargestMaximizer m (fun x => (x : ℝ) * L x) y := by sorry

end ProductFraming.Trunc
