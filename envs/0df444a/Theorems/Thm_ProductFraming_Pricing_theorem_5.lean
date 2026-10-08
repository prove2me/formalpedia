-- Prove2me | Theorems.Thm_ProductFraming_Pricing_theorem_5
-- name    : ProductFraming.Pricing.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:43.042118+00:00
-- url     : https://prove2.me/theorems/b3d8d7a2-aa81-4486-a71d-9904ac7b1ddc
-- title:
--   Theorem 5 — for a fixed framing, optimal prices are constant on each page and nondecreasing in the page
-- statement:
--   Fix a feasible framing on $m\ge1$ pages of capacity $p\ge1$, a page-count law $\lambda$ on $[m]$, qualities $a\in\mathbb R^n$ and $\beta>0$. Let $r\in\mathbb R^n$ maximize the total expected revenue $\mathbf E[R(r\mid S(X))]$ over all price vectors. Then there are page prices $\theta_1,\dots,\theta_m$ such that
--
--   1. $r_i=\theta_x$ for every product $i$ displayed on page $x$ with $\Lambda(x)=\mathbf P[X\ge x]>0$, and
--   2. $$\theta_1\le\theta_2\le\cdots\le\theta_m.$$
--
--   This extends the classical fact that the optimal MNL prices are all equal: with framing, the equal-price structure holds page by page, and consumers who view more pages see higher prices on the later pages.
--
--   **Formalization Note.** The statement holds for every maximizer $r$ (the paper's "we must have"). Prices of undisplayed products are unconstrained, and $\theta_x$ for an empty page is only required to fit the monotone chain. The price equality is required only on pages that some consumer reaches ($\Lambda(x)>0$): a product on a page that no consumer reaches does not affect the revenue and can carry any price at an optimum, a case the paper does not consider. When $\lambda(m)>0$ every page is reached and the statement is the paper's verbatim.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 16, Theorem 5 (proof A.5, pp. 43–44)

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model
open Finset

namespace ProductFraming.Pricing

theorem theorem_5 {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (r : Fin n → ℝ)
    (hr : ∀ r' : Fin n → ℝ, totalRevenue m a β lam f r' ≤ totalRevenue m a β lam f r) :
    ∃ θ : ℕ → ℝ, (∀ i, 1 ≤ f i → 0 < ProductFraming.Nest.tail m lam (f i) → r i = θ (f i)) ∧
      ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' → θ x ≤ θ x' := by sorry

end ProductFraming.Pricing
