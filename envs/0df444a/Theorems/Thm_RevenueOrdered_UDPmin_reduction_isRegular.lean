-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_reduction_isRegular
-- name    : RevenueOrdered.UDPmin.reduction_isRegular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:16.545647+00:00
-- url     : https://prove2.me/theorems/44a1461b-365d-48cc-8354-385592315713
-- title:
--   The choice model $\mathcal P=\frac1m\sum_i\mathcal P_i$ of Theorem 4.6 is regular
-- statement:
--   For every $\mathrm{UDP}_{\min}$ instance with at least one consumer, the choice model $\mathcal P(y,S)=\frac1m\sum_{i=1}^m\mathcal P_i(y,S)$ on $\mathcal C=[n]\times\{v_1,\dots,v_m\}$, where $\mathcal P_i$ spreads probability $1$ uniformly over the set $Q_i(S)$ of cheapest acceptable copies of consumer $i$'s items, is a **regular discrete choice model**: it satisfies axioms (i)–(iv), including
--   $$\mathcal P(0,S)\ \ge\ \mathcal P(0,S')\qquad\text{for all } S\subseteq S'\subseteq\mathcal C.$$
--
--   This is the part of Theorem 4.6 that places $\mathrm{UDP}_{\min}$ inside the scope of the paper's guarantees for regular models.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, §4.5.1, proof of Theorem 4.6, pp. 17–18

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Definitions.Def_RevenueOrdered_UDPmin_Pricing
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

namespace RevenueOrdered.UDPmin

/-- The choice model of Theorem 4.6 is regular (Berbeglia–Joret, arXiv:1606.01371v3, §4.5.1,
proof of Theorem 4.6, pp. 17–18). -/
theorem reduction_isRegular {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    IsRegular (redP I) := by sorry

end RevenueOrdered.UDPmin
