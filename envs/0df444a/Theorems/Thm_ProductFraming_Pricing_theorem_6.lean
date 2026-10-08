-- Prove2me | Theorems.Thm_ProductFraming_Pricing_theorem_6
-- name    : ProductFraming.Pricing.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:17.906199+00:00
-- url     : https://prove2.me/theorems/3c8da5fb-3141-437b-8fcf-c9fc1aab011d
-- title:
--   Theorem 6 — some optimal joint pricing-and-framing solution fills pages in order with products of descending quality
-- statement:
--   Consider $n$ products with qualities $a_1,\dots,a_n\in\mathbb R$, MNL choice with utilities $u_i=a_i-\beta r_i$ and price sensitivity $\beta>0$, $m\ge1$ pages of capacity $p\ge1$, and a page-count law $\lambda$ on $[m]$. The retailer chooses jointly a feasible framing and a price vector $r\in\mathbb R^n$ to maximize the total expected revenue $\mathbf E[R(r\mid S(X))]=\sum_{x=1}^m\lambda(x)R(r\mid S(x))$.
--
--   Then there is an optimal solution — a feasible framing with consideration sets $S(\cdot)$ and prices $r$ such that no feasible framing with any prices earns more — with the following structure:
--
--   1. **Pages are filled in order until all products are displayed:** for every $x\in[m]$,
--   $$|S(x)| = \min(n,\ x\,p).$$
--   2. **Descending quality:** if product $i$ is displayed and product $k$ is either not displayed or displayed on a later page than $i$, then $a_k\le a_i$.
--
--   This is the structural result behind the paper's approximation algorithm for joint pricing and framing: once the framing is known to be "sort by quality and fill", only the page boundaries and the page prices of Theorem 5 remain to be chosen.
--
--   **Formalization Note.** "At optimality" is read existentially: some joint optimum has this structure. The universal reading fails in degenerate instances (if $\lambda(x)=0$, swapping products between pages $x$ and $x+1$ changes no revenue). The optimum ranges over all feasible framings and all real price vectors, and the statement asserts that a joint optimum exists. Undisplayed products are those with page $0$; "descending order" is weak (ties allowed).
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 17, Theorem 6 (proof A.5, pp. 44–45)

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model
open Finset

namespace ProductFraming.Pricing

theorem theorem_6 {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam) :
    ∃ f : Fin n → ℕ, ∃ r : Fin n → ℝ, ProductFraming.Trunc.Feasible m p f ∧
      (∀ (f' : Fin n → ℕ) (r' : Fin n → ℝ), ProductFraming.Trunc.Feasible m p f' →
        totalRevenue m a β lam f' r' ≤ totalRevenue m a β lam f r) ∧
      (∀ x ∈ Icc 1 m, (ProductFraming.Nest.consideration f x).card = min n (x * p)) ∧
      (∀ i k : Fin n, 1 ≤ f i → (f k = 0 ∨ f i < f k) → a k ≤ a i) := by sorry

end ProductFraming.Pricing
