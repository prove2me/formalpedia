-- Prove2me | Theorems.Thm_SalesTrust_Sharing_proposition_3
-- name    : SalesTrust.Sharing.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:14.699068+00:00
-- url     : https://prove2.me/theorems/5c675f9e-a667-4811-a045-1ef91394101d
-- title:
--   Proposition 3, p. 17 — sharing past sales information benefits the retailer iff δ ≤ δ̃ = 1/(1+√(1+p))
-- statement:
--   A manufacturer sells to a retailer in an infinitely repeated game; demand is high with probability $p$ and low with probability $1-p$, i.i.d. across periods, with linear inverse demand $V_\theta - q$, and only the retailer observes the current state. Both firms discount with factor $\delta$. Assume $0<p<1$, $V_L<V_H$, $pV_H<V_L$ and $0\le\delta<1$.
--
--   Let $m^{ne}$ be any manufacturer-optimal menu of the program without sales information ((8)–(9): dynamic participation, static incentive constraints) and $m^{e}$ any manufacturer-optimal menu of the program with past sales information ((17)–(18): dynamic participation and dynamic incentive constraints). Write $\Pi^{D,ne}_R$ and $\Pi^{D,e}_R$ for the retailer's expected per-period profit $p(\pi_R(q_H;H) - T_H) + (1-p)(\pi_R(q_L;L) - T_L)$ at these menus. Then
--   $$\Pi^{D,e}_R \ \ge\ \Pi^{D,ne}_R \quad\Longleftrightarrow\quad \delta \ \le\ \tilde\delta = \frac{1}{1+\sqrt{1+p}}.$$
--
--   Sharing past sales information always helps the manufacturer; this theorem identifies exactly when the retailer, who decides whether to share, is also better off, which is when sharing can arise in equilibrium.
--
--   **Formalization Note** The threshold is written explicitly rather than as "there is a threshold". The statement quantifies over every optimal menu of each program; Propositions 1 and 2 show that each program has exactly one. $\delta<1$ is added to the paper's $0\le\delta\le1$ because the constraints divide by $1-\delta$; nonnegative quantities are required of every menu.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 17 (PDF 18), Proposition 3, (22)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- Proposition 3, p. 17: sharing past sales information benefits the retailer,
`Π^{D,e}_R ≥ Π^{D,ne}_R`, if and only if `δ ≤ δ̃ = 1/(1 + √(1 + p))`, where `Π^{D,ne}_R` and
`Π^{D,e}_R` are the retailer's expected per-period profits at any manufacturer-optimal menu of the
no-sharing program (8)–(9) and of the sharing program (17)–(18). -/
theorem proposition_3 (P : Params) (hS : P.Standing) (mNE mE : Menu)
    (hNE : IsOptimalNE P mNE) (hE : IsOptimalE P mE) :
    retailerProfit P mNE ≤ retailerProfit P mE ↔ P.δ ≤ deltaTilde P := by sorry

end SalesTrust.Sharing
