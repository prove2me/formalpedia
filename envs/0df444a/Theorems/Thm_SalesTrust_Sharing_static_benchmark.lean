-- Prove2me | Theorems.Thm_SalesTrust_Sharing_static_benchmark
-- name    : SalesTrust.Sharing.static_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:12.166225+00:00
-- url     : https://prove2.me/theorems/8290f8ac-a661-4f8e-9176-c5088ca53245
-- title:
--   (4)–(5), p. 8 — the static optimal menu, and Π^S_R = pΔ(q^S_L)
-- statement:
--   Consider the one-period screening problem: the manufacturer chooses a menu $\{(q_H,T_H),(q_L,T_L)\}$ with $q_H, q_L \ge 0$ to maximize $pT_H + (1-p)T_L$ subject to the participation constraints (1) and incentive constraints (2). Assume $0<p<1$, $V_L<V_H$, $pV_H<V_L$ and $0\le\delta<1$.
--
--   Then the static menu
--   $$q^S_H = \frac{V_H}{2},\quad q^S_L = \frac{V_L}{2} - \frac{p}{1-p}\,\frac{V_H - V_L}{2},\quad T^S_H = \frac{V_H^2}{4} - \frac{(V_L - pV_H)(V_H - V_L)}{2(1-p)},\quad T^S_L = \frac{V_L^2}{4} - \frac{p^2(V_H - V_L)^2}{4(1-p)^2}$$
--   is optimal, it is the only optimal menu, and at it the retailer's expected profit is $\Pi^S_R = p\,\Delta(q^S_L)$.
--
--   The static menu is both the benchmark of the paper and the punishment that sustains the dynamic menus: its rent $p\Delta(q^S_L)$ is the right-hand side of the dynamic constraints (6)–(7).
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 8 (PDF 9), §3.3, (4)–(5), footnote 2; p. 9 (PDF 10), Π^S_R = pΔ(q^S_L)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- §3.3, (4)–(5), p. 8, and p. 9: the static menu is the unique manufacturer-optimal menu
of the program (1)–(2), and the retailer earns `Π^S_R = p Δ(q^S_L)` in expectation. -/
theorem static_benchmark (P : Params) (hS : P.Standing) :
    IsOptimalS P (menuS P) ∧ (∀ m, IsOptimalS P m → m = menuS P) ∧
      retailerProfit P (menuS P) = staticRent P := by sorry

end SalesTrust.Sharing
