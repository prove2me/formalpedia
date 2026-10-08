-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_revenue_assortmentOfPrices_eq
-- name    : RevenueOrdered.Stackelberg.revenue_assortmentOfPrices_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:55.512338+00:00
-- url     : https://prove2.me/theorems/9e5e850b-6426-4491-b333-51e7ef6f920a
-- title:
--   Proof of Theorem 4.16, pp. 34–35 — for prices in $\{c_1,\dots,c_k\}\cup\{+\infty\}$, $\mathrm{rev}(S_p)$ equals the Stackelberg revenue of $p$
-- statement:
--   In the assortment instance built from a Stackelberg Matroid instance $(M,R,B,c)$ (with an admissible ordering $L$ of $R\cup\mathcal C$), let $p:B\to\mathbb R_{>0}$ take every value either in $\{c_1,\dots,c_k\}$ or above every red cost (the paper's $+\infty$), and let $L^*$ be an ordering of $R\cup B$ the customer may use under $p$. Put
--   $$
--   S_p=\{(e,p(e)): e\in\mathrm{greedy}_M(R\cup B,L^*)\}\subseteq\mathcal C.
--   $$
--   Then
--   $$
--   \sum_{y\in S_p}\mathcal P(y,S_p)\,r(y)=\sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L^*)}p(e).
--   $$
--   Together with the rounding step, this shows that the optimum of the assortment instance is at least the optimum of the Stackelberg Matroid instance.
--
--   **Formalization Note** $S_p$ is formalized as the set of products $(e,q)\in\mathcal C$ with $e\in\mathrm{greedy}_M(R\cup B,L^*)$ and $q=p(e)$. Note that $\mathcal P$ is defined with the fixed ordering $L$ of $R\cup\mathcal C$, not with the ordering induced by $L^*$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 34–35, proof of Theorem 4.16

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- Proof of Theorem 4.16, pp. 34–35 (Berbeglia–Joret, arXiv:1606.01371v3): for a price
assignment `p` whose blue prices are red cost levels `c_i` or exceed every red cost (the paper's
`+∞`), and an ordering `L*` the customer may use, the assortment
`S_p = {(e, p(e)) : e ∈ greedy_M(R ∪ B, L*)}` earns the Stackelberg RevenueOrdered.Ratio.revenue of `p`. -/
theorem revenue_assortmentOfPrices_eq {α : Type*} (I : Instance α)
    (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L) (p : α → ℝ)
    (hp : ∀ e ∈ I.B, 0 < p e) (hlev : ∀ e ∈ I.B, p e ∈ costs I ∨ ∀ f ∈ I.R, I.c f < p e)
    (L' : List α) (hL' : I.IsCustomerOrder p L') :
    RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (assortmentOfPrices I p L') =
      I.stackRevenue p L' := by sorry

end RevenueOrdered.Stackelberg
