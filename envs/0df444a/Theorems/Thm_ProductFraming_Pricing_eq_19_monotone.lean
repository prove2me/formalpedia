-- Prove2me | Theorems.Thm_ProductFraming_Pricing_eq_19_monotone
-- name    : ProductFraming.Pricing.eq_19_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:27.166466+00:00
-- url     : https://prove2.me/theorems/091476c6-de72-4fdc-a912-bb7c8e6d7677
-- title:
--   (19) — the optimal expected revenue is nondecreasing in the quality of a displayed product
-- statement:
--   Fix a feasible framing on $m\ge1$ pages of capacity $p\ge1$, a page-count law $\lambda$ on $[m]$ and $\beta>0$. For a quality vector $a\in\mathbb R^n$ let
--   $$
--   R(a)=\sup_{r\in\mathbb R^n}\sum_{x=1}^m\lambda(x)\,R\big(r\mid S(x)\big)
--   $$
--   be the optimal expected revenue of the framing. Let $i$ be a displayed product and let $a'$ agree with $a$ except that $a'_i = t \ge a_i$. Then both suprema are finite (the revenues are bounded above) and
--   $$
--   R(a)\le R(a').
--   $$
--
--   In the paper this is the conclusion drawn from the envelope formula (19), $\partial R(a)/\partial a_i=\frac1\beta\sum_{l=x(i)}^m\lambda(l)P(i,S(l))\ge0$: the total expected revenue increases in the quality of any displayed product. It is what makes filling pages with the best products optimal in Theorem 6.
--
--   **Formalization Note.** The envelope identity (19) itself presupposes a differentiable selection of optimal prices $r(a)$, which the paper does not establish; the milestone states its stated consequence, the monotonicity of the optimal value, instead. "Increases" is read weakly. The boundedness clauses make the real supremum meaningful.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.5, Proof of Theorem 6, p. 44, eq. (19) and the sentence following it

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model
open Finset

namespace ProductFraming.Pricing

theorem eq_19_monotone {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f) (i : Fin n) (hi : 1 ≤ f i) (t : ℝ) (ht : a i ≤ t) :
    BddAbove (Set.range (totalRevenue m a β lam f)) ∧
      BddAbove (Set.range (totalRevenue m (Function.update a i t) β lam f)) ∧
      optRevenue m a β lam f ≤ optRevenue m (Function.update a i t) β lam f := by sorry

end ProductFraming.Pricing
