-- Prove2me | Theorems.Thm_ProductFraming_Trunc_lemma_8
-- name    : ProductFraming.Trunc.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:46.702147+00:00
-- url     : https://prove2.me/theorems/cb44a349-0c31-4912-9145-e7ada5bb6309
-- title:
--   Lemma 8 — under IFR, $g(x)=x\Lambda(x)$ is weakly unimodal with largest maximizer $\min\{x: h(x)>1/(x+1)\}$
-- statement:
--   Let $m\ge 1$ and let $\Lambda$ be a tail function on $[m]$ with $\Lambda(1)=1$, $\Lambda$ nonincreasing, and the IFR (log-concavity) condition $\Lambda(x+1)\Lambda(x-1)\le\Lambda(x)^2$ for $x=2,\dots,m-1$. Suppose $\Lambda(x)>0$ for all $x\in[m]$. Let $\lambda(x)=\Lambda(x)-\Lambda(x+1)$ (with $\Lambda(m+1)=0$), $h(x)=\lambda(x)/\Lambda(x)$ and $g(x)=x\Lambda(x)$. Then:
--
--   1. $g$ is **weakly unimodal**: there is $z\in[m]$ with
--   $$g(x)\le g(x+1)\ \ (1\le x<z),\qquad g(x)>g(x+1)\ \ (z\le x<m);$$
--   2. the largest maximizer of $g$ on $[m]$ is
--   $$\operatorname{maxarg\,max}_{x\in[m]}g(x)=\min\{x\in[m]: h(x)>1/(x+1)\}.$$
--
--   In the analysis of program (10) this identifies the page $y$ at which the optimal solution's objective is attained.
--
--   **Formalization Note** The equality of item 2 is stated as the existence of a $z$ that is both the largest maximizer of $g$ on $[m]$ and the least element of $\{x\in[m]:1/(x+1)<h(x)\}$; both are unique when they exist. Positivity of $\Lambda$ on $[m]$ is the standing assumption of Appendix A.4.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.4, p. 40, Lemma 8 (with the A.4 preamble, p. 39)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Program10
open Finset

namespace ProductFraming.Trunc

theorem lemma_8 (m : ℕ) (hm : 1 ≤ m) (L : ℕ → ℝ) (h_one : L 1 = 1)
    (h_antitone : ∀ x : ℕ, 1 ≤ x → x < m → L (x + 1) ≤ L x)
    (h_ifr : ∀ x : ℕ, 2 ≤ x → x + 1 ≤ m → L (x + 1) * L (x - 1) ≤ L x ^ 2)
    (h_pos : ∀ x ∈ Icc 1 m, 0 < L x) :
    (∃ z ∈ Icc 1 m,
        (∀ x : ℕ, 1 ≤ x → x < z → (x : ℝ) * L x ≤ ((x + 1 : ℕ) : ℝ) * L (x + 1)) ∧
        (∀ x : ℕ, z ≤ x → x < m → ((x + 1 : ℕ) : ℝ) * L (x + 1) < (x : ℝ) * L x)) ∧
    ∃ z : ℕ, IsLargestMaximizer m (fun x => (x : ℝ) * L x) z ∧
      IsLeast {x : ℕ | x ∈ Icc 1 m ∧ 1 / ((x : ℝ) + 1) < hazard m L x} z := by sorry

end ProductFraming.Trunc
