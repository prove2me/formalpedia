-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_roundUp_revenue_le
-- name    : RevenueOrdered.Stackelberg.roundUp_revenue_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:53.30498+00:00
-- url     : https://prove2.me/theorems/49e7cd1b-808f-4ac1-95ba-a4c43d38a26a
-- title:
--   Proof of Theorem 4.16, p. 34 — rounding blue prices up to the red cost levels keeps $L^*$ valid and does not decrease revenue
-- statement:
--   Let $(M,R,B,c)$ be a Stackelberg Matroid instance with distinct red costs $c_1<\dots<c_k$, let $p:B\to\mathbb R_{>0}$ be a price assignment and $L^*$ an ordering of $R\cup B$ the customer may use under $p$. Define the rounded prices
--   $$
--   \hat p(e)=\begin{cases}\min\{c_i: c_i\ge p(e)\}&\text{if } p(e)\le c_k,\\ +\infty&\text{if } p(e)>c_k.\end{cases}
--   $$
--   Then $L^*$ is still an ordering the customer may use under $\hat p$, and the revenue does not decrease:
--   $$
--   \sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L^*)}p(e)\le\sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L^*)}\hat p(e).
--   $$
--
--   This justifies restricting attention to prices in $\{c_1,\dots,c_k\}\cup\{+\infty\}$ when bounding the Stackelberg optimum from above. The paper asserts it, noting that a blue element priced above $c_k$ is never bought because $R$ contains a base.
--
--   **Formalization Note** The price $+\infty$ is `abovePrice` $=1+\sum_{f\in R}c(f)$. The paper modifies $p$ one element at a time; here all prices are rounded at once.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 34, proof of Theorem 4.16

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- Proof of Theorem 4.16, p. 34 (Berbeglia–Joret, arXiv:1606.01371v3): rounding every blue
price up to the next red cost level `c_i` (or to `+∞` if it exceeds `c_k`) keeps the
customer's ordering valid and does not decrease the RevenueOrdered.Ratio.revenue. -/
theorem roundUp_revenue_le {α : Type*} (I : Instance α) (p : α → ℝ)
    (hp : ∀ e ∈ I.B, 0 < p e) (L' : List α) (hL' : I.IsCustomerOrder p L') :
    I.IsCustomerOrder (roundUp I p) L' ∧
      I.stackRevenue p L' ≤ I.stackRevenue (roundUp I p) L' := by sorry

end RevenueOrdered.Stackelberg
