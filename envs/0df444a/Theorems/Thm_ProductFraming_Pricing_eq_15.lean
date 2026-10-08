-- Prove2me | Theorems.Thm_ProductFraming_Pricing_eq_15
-- name    : ProductFraming.Pricing.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:47.81001+00:00
-- url     : https://prove2.me/theorems/20baf6b1-5892-4cd2-b615-ce5ef6e49ea9
-- title:
--   (15) — gradient of the expected revenue in the price of a displayed product
-- statement:
--   Fix a feasible framing on $m\ge1$ pages of capacity $p\ge1$, a page-count law $\lambda$ on $[m]$, qualities $a\in\mathbb R^n$, a price sensitivity $\beta>0$ and a price vector $r\in\mathbb R^n$. Let $i$ be a displayed product and $x(i)\in[m]$ its page, and write $S(l)$ for the products on pages $1,\dots,l$. Then the total expected revenue $\mathbf E[R(r\mid S(X))]=\sum_{l=1}^m\lambda(l)R(r\mid S(l))$ is differentiable in $r_i$ (all other prices held fixed), with
--   $$
--   \frac{\partial\, \mathbf E[R(r\mid S(X))]}{\partial r_i} = \beta \sum_{l=x(i)}^{m} \lambda(l)\,P\big(i,S(l)\big)\Big\{\frac1\beta + R\big(r\mid S(l)\big) - r_i\Big\}.
--   $$
--
--   This is the gradient from which the first-order condition (17) and the page-level price structure of Theorem 5 are derived.
--
--   **Formalization Note.** The derivative is stated as `HasDerivAt` of $t\mapsto \mathbf E[R(r^{(i\leftarrow t)}\mid S(X))]$ at $t=r_i$, where $r^{(i\leftarrow t)}$ replaces the $i$-th price by $t$. Only displayed products ($1\le x(i)\le m$) are covered; for an undisplayed product the paper sets $x(i)=m+1$ and the sum is empty.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.5, Proof of Theorem 5, p. 43, eq. (15)

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model
open Finset

namespace ProductFraming.Pricing

theorem eq_15 {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (r : Fin n → ℝ) (i : Fin n) (hi : 1 ≤ f i) :
    HasDerivAt (fun t : ℝ => totalRevenue m a β lam f (Function.update r i t))
      (β * ∑ l ∈ Icc (f i) m, lam l * mnl a β r (ProductFraming.Nest.consideration f l) i *
        (1 / β + revenue a β r (ProductFraming.Nest.consideration f l) - r i)) (r i) := by sorry

end ProductFraming.Pricing
