-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_udpmin_reduction
-- name    : RevenueOrdered.UDPmin.udpmin_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:46.894413+00:00
-- url     : https://prove2.me/theorems/a2d01eff-fba0-4ee1-8b6b-03287c5f3ac9
-- title:
--   Theorem 4.6 — $\mathrm{UDP}_{\min}$ is an assortment problem under a regular choice model, with uniform pricing = revenue-ordered assortments
-- statement:
--   Fix a $\mathrm{UDP}_{\min}$ instance with items $[n]$, consumers $[m]$ ($m\ge 1$), interest sets $B_i$ and valuations $v_i>0$, and let $(\mathcal C,r,\mathcal P)$ be the assortment instance of the proof of Theorem 4.6: $\mathcal C=[n]\times\{v_1,\dots,v_m\}$, $r((x,v))=m\cdot v$, $\mathcal P=\frac1m\sum_i\mathcal P_i$. Then:
--
--   1. $\mathcal P$ is a regular discrete choice model;
--   2. $r(y)>0$ for every $y\in\mathcal C$;
--   3. the two instances have the same optimal revenue: $\max_{S\subseteq\mathcal C}\sum_{y\in S}\mathcal P(y,S)r(y)=\mathrm{OPT}_{\mathrm{UDP}}$;
--   4. for each consumer $i$, the assortment $\{y'\in\mathcal C: r(y')\ge m\,v_i\}$ has the same revenue as the uniform price $v_i$ on every item;
--   5. for each $y\in\mathcal C$ there is a consumer $i$ such that the assortment $\{y'\in\mathcal C: r(y')\ge r(y)\}$ has the same revenue as the uniform price $v_i$ on every item.
--
--   Items 4 and 5 are the paper's two bullets: uniform pricing on the pricing instance and revenue-ordered assortments on the assortment instance are the same strategy.
--
--   **Formalization Note** The paper states Theorem 4.6 as "one can define an instance"; it is formalized here for the explicit instance of its proof, since the bare existence of a regular instance with the same optimum is met by a single product. In the paper's first bullet the threshold is $r(y)$ for some $y\in\mathcal C$; item 4 names it, $r((x,v_i))=m\,v_i$ for any item $x$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 17, Theorem 4.6 (proof pp. 17–19)

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Definitions.Def_RevenueOrdered_UDPmin_Pricing
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

namespace RevenueOrdered.UDPmin

/-- Theorem 4.6 (Berbeglia–Joret, arXiv:1606.01371v3, p. 17), for the explicit instance of its
proof: the choice model `redP I` on `𝒞 = X × {v_1, …, v_m}` with revenues `r((x, v)) = m·v` is
regular with positive revenues, has the same optimal revenue as the `UDP_min` instance, and
its threshold sets have exactly the revenues of the uniform valuation prices. -/
theorem udpmin_reduction {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    IsRegular (redP I) ∧
    (∀ y : RedProd I, 0 < redRev I y) ∧
    RevenueOrdered.Ratio.opt (redP I) (redRev I) = optUDP I ∧
    (∀ i : M, RevenueOrdered.Tightness.rev (redP I) (redRev I)
        (thresholdSet (redRev I) ((Fintype.card M : ℝ) * I.v i)) = revenue I (fun _ => I.v i)) ∧
    (∀ y : RedProd I, ∃ i : M, RevenueOrdered.Tightness.rev (redP I) (redRev I)
        (thresholdSet (redRev I) (redRev I y)) = revenue I (fun _ => I.v i)) := by sorry

end RevenueOrdered.UDPmin
