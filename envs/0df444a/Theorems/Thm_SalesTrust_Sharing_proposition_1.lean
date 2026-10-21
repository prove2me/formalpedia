-- Prove2me | Theorems.Thm_SalesTrust_Sharing_proposition_1
-- name    : SalesTrust.Sharing.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:01.74598+00:00
-- url     : https://prove2.me/theorems/aee0cdca-155f-4812-a781-78edcb1c0a7b
-- title:
--   Proposition 1, p. 12 — the optimal dynamic menu without sales information, (11)–(12)
-- statement:
--   Assume $0<p<1$, $V_L<V_H$, $pV_H<V_L$ and $0\le\delta<1$, and consider the no-sharing program: maximize $pT_H + (1-p)T_L$ over menus with $q_H, q_L \ge 0$ subject to the dynamic participation constraints $IR^D_\theta$ (8) and the static incentive constraints $IC^S_\theta$ (9).
--
--   The menu
--   $$q^{D,ne}_H = \frac{V_H}{2},\qquad q^{D,ne}_L = q^S_L + \delta\,\frac{p}{1-p}\,\frac{V_H - V_L}{2},$$
--   $$T^{D,ne}_H = T^S_H - \frac{\delta p(1-\delta p)(V_H - V_L)^2}{2(1-p)},\qquad T^{D,ne}_L = T^S_L + \frac{\delta p^2\,(2(1-\delta p) + \delta)(V_H - V_L)^2}{4(1-p)^2}$$
--   is optimal, and it is the only optimal menu.
--
--   Repeated interaction alone, without any information about past demand, raises the low-state quantity above the static $q^S_L$; this is the benchmark against which sharing is measured.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 12 (PDF 13), Proposition 1, (11)–(12)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- Proposition 1, p. 12: without sales information the manufacturer-optimal menu of the
program (8)–(9) is the menu (11)–(12), and it is the only one. -/
theorem proposition_1 (P : Params) (hS : P.Standing) :
    IsOptimalNE P (menuNE P) ∧ ∀ m, IsOptimalNE P m → m = menuNE P := by sorry

end SalesTrust.Sharing
