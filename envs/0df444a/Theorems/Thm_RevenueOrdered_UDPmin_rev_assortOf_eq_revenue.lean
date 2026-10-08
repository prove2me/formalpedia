-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_rev_assortOf_eq_revenue
-- name    : RevenueOrdered.UDPmin.rev_assortOf_eq_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:36.500777+00:00
-- url     : https://prove2.me/theorems/94130490-b020-4310-abcf-0956431064bc
-- title:
--   For valuation-valued prices $p$, the revenue of the assortment $S_p$ equals that of $p$
-- statement:
--   In the assortment instance built from a $\mathrm{UDP}_{\min}$ instance with at least one consumer (Theorem 4.6), let $p$ be a price assignment with $p(x)\in\{v_1,\dots,v_m\}$ for every item $x$, and let $S_p=\{(x,v)\in\mathcal C: v\ge p(x)\}$. Then
--   $$\sum_{y\in S_p}\mathcal P(y,S_p)\,r(y)\ =\ \mathrm{rev}_{\mathrm{UDP}}(p).$$
--
--   Combined with Lemma 4.5, this shows that the optimum of the pricing instance is at most that of the assortment instance.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, §4.5.1, proof of Theorem 4.6, p. 19

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Definitions.Def_RevenueOrdered_UDPmin_Pricing
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

namespace RevenueOrdered.UDPmin

/-- For a price assignment `p` all of whose prices are valuations, the revenue of the assortment
`S_p` equals the revenue of `p` (Berbeglia–Joret, arXiv:1606.01371v3, §4.5.1, proof of
Theorem 4.6, p. 19). -/
theorem rev_assortOf_eq_revenue {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) (p : X → ℝ) (hp : ∀ x, ∃ i, p x = I.v i) :
    RevenueOrdered.Tightness.rev (redP I) (redRev I) (assortOf I p) = revenue I p := by sorry

end RevenueOrdered.UDPmin
