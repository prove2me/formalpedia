-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_rev_eq_revenue_priceOf
-- name    : RevenueOrdered.UDPmin.rev_eq_revenue_priceOf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:27.525197+00:00
-- url     : https://prove2.me/theorems/e634e5f5-d25a-47c0-990d-ba7e3fb3aaa3
-- title:
--   The revenue of an assortment $S$ equals the revenue of its price assignment $p_S$
-- statement:
--   In the assortment instance built from a $\mathrm{UDP}_{\min}$ instance with at least one consumer (Theorem 4.6), for every assortment $S\subseteq\mathcal C=[n]\times\{v_1,\dots,v_m\}$,
--   $$\sum_{y\in S}\mathcal P(y,S)\,r(y)\ =\ \mathrm{rev}_{\mathrm{UDP}}(p_S),$$
--   where $p_S(x)=\min\{v:(x,v)\in S\}$, and $p_S(x)$ is a price above every valuation when $S$ contains no pair with first coordinate $x$.
--
--   Consequently the optimum of the assortment instance is at most that of the pricing instance.
--
--   **Formalization Note** The paper's $+\infty$ price is the real $1+\sum_i v_i$ (Remark, p. 18).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, §4.5.1, proof of Theorem 4.6, p. 19

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Definitions.Def_RevenueOrdered_UDPmin_Pricing
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

namespace RevenueOrdered.UDPmin

/-- The revenue of an assortment `S` of the Theorem 4.6 instance equals the revenue of its price
assignment `p_S` (Berbeglia–Joret, arXiv:1606.01371v3, §4.5.1, proof of Theorem 4.6, p. 19). -/
theorem rev_eq_revenue_priceOf {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) (S : Finset (RedProd I)) :
    RevenueOrdered.Tightness.rev (redP I) (redRev I) S = revenue I (priceOf I S) := by sorry

end RevenueOrdered.UDPmin
