-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_revenue_eq_stackRevenue_priceOfAssortment
-- name    : RevenueOrdered.Stackelberg.revenue_eq_stackRevenue_priceOfAssortment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:40.474562+00:00
-- url     : https://prove2.me/theorems/6c5f1810-3652-4b44-98d9-744260700dcd
-- title:
--   Proof of Theorem 4.16, pp. 33–34 — $\mathrm{rev}(S)$ equals the Stackelberg revenue of $p_S$
-- statement:
--   In the assortment instance built from a Stackelberg Matroid instance $(M,R,B,c)$ (with an admissible ordering $L$ of $R\cup\mathcal C$), let $S\subseteq\mathcal C$ and let $p_S$ be the price assignment
--   $$
--   p_S(e)=\begin{cases}\min\{q:(e,q)\in S\} & \text{if some }(e,q)\in S,\\ +\infty&\text{otherwise.}\end{cases}
--   $$
--   Then for every ordering $L^*$ of $R\cup B$ that the customer may use under $p_S$ (compatible with the costs and prices, blue first on ties),
--   $$
--   \sum_{y\in S}\mathcal P(y,S)\,r(y)=\sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L^*)}p_S(e).
--   $$
--   Consequently the optimum of the Stackelberg Matroid instance is at least the optimum of the assortment instance.
--
--   **Formalization Note** The price $+\infty$ is the real number `abovePrice` $=1+\sum_{f\in R}c(f)$, strictly larger than every red cost; such a blue element is never bought because $R$ contains a base.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 33–34, proof of Theorem 4.16

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- Proof of Theorem 4.16, pp. 33–34 (Berbeglia–Joret, arXiv:1606.01371v3): the RevenueOrdered.Ratio.revenue of an
assortment `S ⊆ 𝒞` equals the Stackelberg RevenueOrdered.Ratio.revenue of the price assignment `p_S`
(`p_S(e) = min{q : (e, q) ∈ S}`, or `+∞` if there is no such pair), for every ordering the
customer may use under `p_S`. -/
theorem revenue_eq_stackRevenue_priceOfAssortment {α : Type*} (I : Instance α)
    (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L) (S : Finset (Product I)) (L' : List α)
    (hL' : I.IsCustomerOrder (priceOfAssortment I S) L') :
    RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) S =
      I.stackRevenue (priceOfAssortment I S) L' := by sorry

end RevenueOrdered.Stackelberg
