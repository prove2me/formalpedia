-- Prove2me | Theorems.Thm_SalesTrust_Sharing_proposition_2
-- name    : SalesTrust.Sharing.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:04.308067+00:00
-- url     : https://prove2.me/theorems/ac6d1fcd-f07a-4d37-84ba-51289d26d77e
-- title:
--   Proposition 2, p. 16 — the optimal dynamic menu with past sales information, (20)–(21)
-- statement:
--   Assume $0<p<1$, $V_L<V_H$, $pV_H<V_L$ and $0\le\delta<1$, and consider the sharing program: maximize $pT_H + (1-p)T_L$ over menus with $q_H, q_L \ge 0$ subject to the dynamic participation constraints $IR^D_\theta$ (17) and the dynamic incentive constraints $IC^D_\theta$ (18).
--
--   The menu
--   $$q^{D,e}_H = \frac{V_H}{2},\qquad q^{D,e}_L = q^S_L + \frac{1+p}{1+\delta p}\,\frac{\delta p}{1-p}\,\frac{V_H - V_L}{2},$$
--   $$T^{D,e}_H = T^S_H - \frac{1+p}{(1+\delta p)^2}\,\frac{\delta p(1-\delta p)(V_H - V_L)^2}{2(1-p)},\qquad T^{D,e}_L = T^S_L + \frac{1+p}{(1+\delta p)^2}\,\frac{\delta p^2\,(2 + \delta(1-p))(V_H - V_L)^2}{4(1-p)^2}$$
--   is optimal, and it is the only optimal menu.
--
--   Sharing past sales information lets the manufacturer detect a misreport and punish it, which loosens the high-state incentive constraint and raises the low-state quantity further.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 16 (PDF 17), Proposition 2, (20)–(21)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- Proposition 2, p. 16: with sales information the manufacturer-optimal menu of the
program (17)–(18) is the menu (20)–(21), and it is the only one. -/
theorem proposition_2 (P : Params) (hS : P.Standing) :
    IsOptimalE P (menuE P) ∧ ∀ m, IsOptimalE P m → m = menuE P := by sorry

end SalesTrust.Sharing
