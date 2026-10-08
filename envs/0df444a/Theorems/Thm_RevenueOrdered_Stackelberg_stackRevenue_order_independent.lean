-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_stackRevenue_order_independent
-- name    : RevenueOrdered.Stackelberg.stackRevenue_order_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:47.65466+00:00
-- url     : https://prove2.me/theorems/5e95c867-77ec-4a9c-8e5e-0db99bf0331c
-- title:
--   Lemma 4.15 — the Stackelberg revenue does not depend on the customer's compatible ordering
-- statement:
--   Consider a Stackelberg Matroid instance: a matroid $M=(E,\mathcal X)$, a bipartition $E=R\sqcup B$ into red and blue elements, red costs $c:R\to\mathbb R_{>0}$, and a red base of $M$. Let $p:B\to\mathbb R_{>0}$ be a price assignment, and let $L$, $L'$ be two linear orderings of $R\cup B$ compatible with the costs and prices (non-decreasing in weight, blue before red on ties; (15a)–(15b)). Then for every $\gamma\in\mathbb R$,
--   $$
--   \bigl|\{e\in B\cap\mathrm{greedy}_M(R\cup B,L): p(e)=\gamma\}\bigr|=\bigl|\{e\in B\cap\mathrm{greedy}_M(R\cup B,L'): p(e)=\gamma\}\bigr|,
--   $$
--   and in particular the revenue $\sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L)}p(e)$ is the same for $L$ and $L'$.
--
--   This makes the optimum revenue of the Stackelberg Matroid problem well defined, although the customer's ordering is not unique.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 23, Lemma 4.15 (proof pp. 31–32)

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance

open Classical

namespace RevenueOrdered.Stackelberg

/-- Lemma 4.15 (Berbeglia–Joret, arXiv:1606.01371v3, p. 23). In a Stackelberg Matroid instance,
for a price assignment `p : B → ℝ_{>0}` and any two orderings `L`, `L'` of `R ∪ B` compatible
with the costs and prices (non-decreasing, blue before red on ties), the number of bought blue
elements of each price `γ` is the same; in particular the RevenueOrdered.Ratio.revenue is the same. -/
theorem stackRevenue_order_independent {α : Type*} (I : Instance α) (p : α → ℝ)
    (hp : ∀ e ∈ I.B, 0 < p e) (L L' : List α) (hL : I.IsCustomerOrder p L)
    (hL' : I.IsCustomerOrder p L') :
    (∀ γ : ℝ, ((I.B ∩ greedyM I.M L (I.R ∪ I.B)).filter (fun e => p e = γ)).card =
        ((I.B ∩ greedyM I.M L' (I.R ∪ I.B)).filter (fun e => p e = γ)).card) ∧
      I.stackRevenue p L = I.stackRevenue p L' := by sorry

end RevenueOrdered.Stackelberg
