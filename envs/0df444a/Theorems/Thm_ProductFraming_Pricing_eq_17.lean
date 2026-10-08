-- Prove2me | Theorems.Thm_ProductFraming_Pricing_eq_17
-- name    : ProductFraming.Pricing.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:26.07713+00:00
-- url     : https://prove2.me/theorems/0dbdd902-e4ae-42b8-a9b3-5ef50f2aa235
-- title:
--   (17) — first-order condition: an optimal price is a weighted average of $1/\beta + R(r\mid S(l))$
-- statement:
--   Fix a feasible framing on $m\ge1$ pages of capacity $p\ge1$, a page-count law $\lambda$ on $[m]$, qualities $a\in\mathbb R^n$ and $\beta>0$. Let $r\in\mathbb R^n$ be an optimal price vector for this framing, i.e. $\mathbf E[R(r'\mid S(X))]\le \mathbf E[R(r\mid S(X))]$ for every $r'\in\mathbb R^n$. Then for every displayed product $i$, with page $x(i)$, that some consumer sees, i.e. $\Lambda(x(i))=\mathbf P[X\ge x(i)]>0$,
--   $$
--   r_i = \frac{\sum_{l=x(i)}^{m}\lambda(l)\,P\big(i,S(l)\big)\big\{\frac1\beta + R\big(r\mid S(l)\big)\big\}}{\sum_{l=x(i)}^{m}\lambda(l)\,P\big(i,S(l)\big)}.
--   $$
--
--   Thus each optimal price is the constant $1/\beta$ plus a weighted average of the revenues of the consumers who see the product. Since the weights of all products on one page agree up to a common factor, this gives the within-page part of Theorem 5.
--
--   **Formalization Note.** Prices are finite, so $P(i,S(l))>0$ whenever $i\in S(l)$, and the paper's "priced out" branch ($r_i=+\infty$) does not arise; a priced-out product is the same as an undisplayed one. The hypothesis $\Lambda(x(i))>0$ is added: it is exactly the condition that the denominator is positive (so Lean's convention $x/0=0$ never applies); a product that no consumer ever sees has an arbitrary price at an optimum, and the paper does not consider that case. The statement is about every maximizer; it does not assert that one exists.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.5, Proof of Theorem 5, p. 43, eqs. (16)–(17)

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model
open Finset

namespace ProductFraming.Pricing

theorem eq_17 {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (r : Fin n → ℝ)
    (hr : ∀ r' : Fin n → ℝ, totalRevenue m a β lam f r' ≤ totalRevenue m a β lam f r)
    (i : Fin n) (hi : 1 ≤ f i) (hreach : 0 < ProductFraming.Nest.tail m lam (f i)) :
    r i = (∑ l ∈ Icc (f i) m, lam l * mnl a β r (ProductFraming.Nest.consideration f l) i *
              (1 / β + revenue a β r (ProductFraming.Nest.consideration f l))) /
          (∑ l ∈ Icc (f i) m, lam l * mnl a β r (ProductFraming.Nest.consideration f l) i) := by sorry

end ProductFraming.Pricing
