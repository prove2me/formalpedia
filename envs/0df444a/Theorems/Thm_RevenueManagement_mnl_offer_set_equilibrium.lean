-- Prove2me | Theorems.Thm_RevenueManagement_mnl_offer_set_equilibrium
-- name    : RevenueManagement.mnl_offer_set_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:11:51.107989+00:00
-- url     : https://prove2.me/theorems/db51f848-baef-469c-bfba-511e9e2a892a
-- title:
--   Proposition 8.3 (Talluri): when both firms are in Case I, or both in Case II, the one-period MNL offer-set duopoly game has a pure-strategy equilibrium in complete offer sets
-- statement:
--   Two firms with MNL fare products (positive weights, prices decreasing in the product index)
--   and a no-purchase weight $w_0 > 0$ compete in one period of the dynamic game (8.31): firm 1
--   offering its first $k$ products against firm 2's first $l$ earns
--   $g_1(C_k)/(W_1(k) + W_2(l) + w_0)$, with $g_i(C_k) = \sum_{j \in C_k} w^i_j(p^i_j - \Delta_i) - w_0\delta_i$,
--   and firm 2 symmetrically. If both firms are in Case I ($g_i(G^*) \ge 0$) or both in Case II
--   ($g_i < 0$ on every complete set), there is a pure-strategy Nash equilibrium
--   $(C_k, C_l)$ in complete offer sets. The mixed case can fail (Example 8.18).
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 399, Proposition 8.3 ('When both firms are in Case I, or both are in Case II, there exists an equilibrium in offer sets'), proof in Appendix 8.A pp. 404-405, from Talluri [503]

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem mnl_offer_set_equilibrium (A B : OfferFirm) (w0 : ℝ) (hw0 : 0 < w0) (hA : A.IsModel)
    (hB : B.IsModel) (hcase : (A.CaseI w0 ∧ B.CaseI w0) ∨ (A.CaseII w0 ∧ B.CaseII w0)) :
    ∃ k l, IsOfferEquilibrium A B w0 k l := by sorry

end RevenueManagement
