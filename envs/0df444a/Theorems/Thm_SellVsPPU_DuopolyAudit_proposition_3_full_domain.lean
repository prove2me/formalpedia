-- Prove2me | Theorems.Thm_SellVsPPU_DuopolyAudit_proposition_3_full_domain
-- name    : SellVsPPU.DuopolyAudit.proposition_3_full_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:50:35.989709+00:00
-- url     : https://prove2.me/theorems/65badc27-f087-4799-9bee-bb2727496419
-- title:
--   Proposition 3 — exact duopoly profit threshold including zero production cost
-- statement:
--   Let $a>0$, $q_m>0$, $c\ge0$ and $\delta\ge0$, with $c_u=c/q_m+\delta\le a$. A unit mass of customers has real usage $q$ uniformly distributed on $[0,q_m]$. Utilities are $U_s=qa-p_s$ and $U_u=q(a-p_u)$. The weak utility and participation inequalities define $D_s,D_u$. Actual profits are $\Pi_s=(p_s-c)\operatorname{Leb}(D_s)/q_m$ and $\Pi_u=(p_u-c_u)\int_{D_u}q\,dq/q_m$. A global price equilibrium allows every real seller deviation and every provider deviation at most $a$.
--
--   Define the delivery-cost threshold, independently of the delivery cost being tested, by
--
--   $$\bar\delta(c)=\begin{cases}
--   \dfrac{c}{2q_m},&0\le c\le aq_m/3,\\
--   a-\dfrac{c}{q_m}-2a\left(\dfrac{aq_m-c}{aq_m+c}\right)^2,&aq_m/3<c\le aq_m.
--   \end{cases}$$
--
--   A global price equilibrium exists. At every such equilibrium,
--
--   $$\Pi_s(p_s,p_u)\le\Pi_u(p_s,p_u)\quad\Longleftrightarrow\quad\delta\le\bar\delta(c),$$
--
--   and if $\delta>\bar\delta(c)$, then $\Pi_u(p_s,p_u)<\Pi_s(p_s,p_u)$. Both branches, equality at the threshold, zero production cost and the service-feasibility boundary are included. The bound $c\le aq_m$ follows from admissibility.
--
--   This characterizes the relative profitability of the two differentiated business models. For information goods with $c=0$, the threshold is zero, so every strictly positive admissible delivery cost favors selling. The result concerns actual market profits, without assuming the equilibrium table or the desired comparison.
--
--   Differences from the source:
--   - reading: Section 2.1 begins with positive production cost, while Proposition 3 and p. 15 explicitly include zero cost → the admissible domain includes all nonnegative production costs with c/q_m + delta at most a; reason: the explicit domain of the target and its information-goods interpretation determine the full claim
--   - generalization: Proposition 3 compares the equilibrium profits in the displayed table → a global price equilibrium exists and the comparison holds at every global price equilibrium; reason: the tabulated equilibrium is included and no table identity or comparison is assumed
--   - encoding: the threshold is displayed as two formulas separated at c = a q_m / 3 → the published deltaBar function has exactly these branches and depends only on a, q_m and c; reason: naming the piecewise function changes no parameter instance or inequality
-- source:
--   Ladas, Kavadias & Loch, Product Selling Versus Pay-Per-Use Service: A Strategic Analysis of Competing Business Models, SSRN 3356458, manuscript dated 16 April 2021, https://ssrn.com/abstract=3356458, Proposition 3, p. 14; information-goods interpretation, p. 15; Appendix A.2.4, p. 42

import Definitions.Def_SellVsPPU_DuopolyAudit_Domain

namespace SellVsPPU.DuopolyAudit
open SellVsPPU.Duopoly

/-- Proposition 3, p. 14, and the information-goods endpoint, p. 15.
The conclusion includes existence and applies to every global price equilibrium;
no table formula, optimality condition, or profit comparison is a hypothesis. -/
theorem proposition_3_full_domain (P : Params) (hP : Admissible P) :
    (∃ ps pu : ℝ, IsPriceEq P ps pu) ∧
    (∀ ps pu : ℝ, IsPriceEq P ps pu →
      (profitS P ps pu ≤ profitU P ps pu ↔
        P.delta ≤ deltaBar P.a P.qm P.c) ∧
      (deltaBar P.a P.qm P.c < P.delta → profitU P ps pu < profitS P ps pu)) := by sorry

end SellVsPPU.DuopolyAudit
