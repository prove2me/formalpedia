-- Prove2me | Theorems.Thm_SellVsPPU_DuopolyAudit_equilibrium_table_full_domain
-- name    : SellVsPPU.DuopolyAudit.equilibrium_table_full_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:49:56.006293+00:00
-- url     : https://prove2.me/theorems/18fab932-09f3-449b-b47f-e6cd1091e424
-- title:
--   §3.3, p. 13 — full-domain equilibrium table and all-equilibrium profits
-- statement:
--   Let $a>0$, $q_m>0$, $c\ge0$ and $\delta\ge0$, with $c_u=c/q_m+\delta\le a$. A unit mass of customers has real usage $q$ uniformly distributed on $[0,q_m]$. Utilities are $U_s=qa-p_s$ and $U_u=q(a-p_u)$. The weak utility and participation inequalities define $D_s,D_u$. Actual profits are $\Pi_s=(p_s-c)\operatorname{Leb}(D_s)/q_m$ and $\Pi_u=(p_u-c_u)\int_{D_u}q\,dq/q_m$. A global price equilibrium allows every real seller deviation and every provider deviation at most $a$.
--
--   Write $(p_s^*,p_u^*)$ for the following prices and $(T_s,T_u)$ for the following profits. When $2c_u\le a$,
--
--   $$p_s^*=\frac{3c+2\delta q_m}{2},\quad p_u^*=2c_u,\quad
--   T_s=\frac{(c+2\delta q_m)^2}{8(c+\delta q_m)},\quad
--   T_u=\frac{(3c+2\delta q_m)^2}{32(c+\delta q_m)}.$$
--
--   At $c=\delta=0$, both profit entries are explicitly zero. When $a<2c_u$,
--
--   $$p_s^*=\frac{c+aq_m}{2},\quad p_u^*=a,\quad
--   T_s=\frac{(aq_m-c)^2}{4q_ma},\quad
--   T_u=\frac{(q_m(a-\delta)-c)(aq_m+c)^2}{8q_m^2a^2}.$$
--
--   The complete four-row table is realized by a global equilibrium, and its actual profits agree with its entries. Moreover,
--
--   $$\forall (p_s,p_u)\text{ a global equilibrium},\quad
--   \Pi_s(p_s,p_u)=T_s,\qquad\Pi_u(p_s,p_u)=T_u.$$
--
--   This identifies actual customer-market profits on the full nonnegative production-cost domain and supplies the quantities compared in Proposition 3. It imposes no uniqueness of prices at the boundary $c=aq_m,\delta=0$.
--
--   Differences from the source:
--   - reading: Section 2.1 begins with positive production cost, while Proposition 3 and p. 15 explicitly include zero cost → the admissible domain includes all nonnegative production costs with c/q_m + delta at most a; reason: the explicit domain of the target and its information-goods interpretation determine the full claim
--   - generalization: the table is derived through first-order and KKT calculations → the tabulated price pair globally maximizes each actual market profit against every permitted unilateral price deviation; reason: global optimality implies the equilibrium interpretation intended for every table instance
--   - generalization: the table describes the overall solution without an explicit all-equilibrium profit theorem → every global price equilibrium has the same two tabulated profits; reason: this includes the displayed equilibrium and does not assert uniqueness of prices
--   - encoding: both first-regime profit quotients are undefined at c = delta = 0 → both table values are explicitly zero at that origin; reason: the actual model has zero seller and provider margins at free prices, so both actual profits are zero
-- source:
--   Ladas, Kavadias & Loch, Product Selling Versus Pay-Per-Use Service: A Strategic Analysis of Competing Business Models, SSRN 3356458, manuscript dated 16 April 2021, https://ssrn.com/abstract=3356458, §3.3 displayed four-row equilibrium table, p. 13; Appendix A.2.1, pp. 36–37

import Definitions.Def_SellVsPPU_DuopolyAudit_Domain

namespace SellVsPPU.DuopolyAudit
open SellVsPPU.Duopoly

/-- Section 3.3, p. 13, all four rows in both regimes, including c = 0.
The origin uses an explicit zero extension. Global optimality and the profit
identities for every equilibrium are disclosed strengthenings of the table. -/
theorem equilibrium_table_full_domain (P : Params) (hP : Admissible P) :
    IsPriceEq P (psStar P) (puStar P) ∧
    profitS P (psStar P) (puStar P) = tableProfitS P ∧
    profitU P (psStar P) (puStar P) = tableProfitU P ∧
    (2 * cu P ≤ P.a →
      psStar P = (3 * P.c + 2 * P.delta * P.qm) / 2 ∧
      puStar P = 2 * (P.c / P.qm + P.delta) ∧
      tableProfitS P = (if P.c = 0 ∧ P.delta = 0 then 0 else
        (P.c + 2 * P.delta * P.qm) ^ 2 / (8 * (P.c + P.delta * P.qm))) ∧
      tableProfitU P = (if P.c = 0 ∧ P.delta = 0 then 0 else
        (3 * P.c + 2 * P.delta * P.qm) ^ 2 / (32 * (P.c + P.delta * P.qm)))) ∧
    (P.a < 2 * cu P →
      psStar P = (P.c + P.a * P.qm) / 2 ∧
      puStar P = P.a ∧
      tableProfitS P = (P.a * P.qm - P.c) ^ 2 / (4 * P.qm * P.a) ∧
      tableProfitU P = (P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2 /
        (8 * P.qm ^ 2 * P.a ^ 2)) ∧
    (∀ ps pu : ℝ, IsPriceEq P ps pu →
      profitS P ps pu = tableProfitS P ∧ profitU P ps pu = tableProfitU P) := by sorry

end SellVsPPU.DuopolyAudit
