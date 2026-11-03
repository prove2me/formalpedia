-- Prove2me | Theorems.Thm_ReactiveCapacity_table_B
-- name    : ReactiveCapacity.table_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:16.030199+00:00
-- url     : https://prove2.me/theorems/bd5841c4-c66c-4f75-bd3b-891e91c50dfc
-- title:
--   Table B: under medium reactive capacity the equilibrium is opportunistic targeting with stockout or with overstock, whichever pays the retailer more (corrected: domain)
-- statement:
--   Assume the standing assumptions, the focus condition and high-only dominance, and let $0\le\bar Q\le 1-\alpha_g$. Write $Y=Y(\alpha_g+\bar Q)$ and $X=Y(1)$. Then an equilibrium exists, and every equilibrium outcome is one of the two columns of Table B:
--
--   1. **opportunistic targeting with stockout**, possible only when $V_{OS}(\bar Q)\ge V_{OO}$:
--   $$
--   \pi_R^*=V_{OS}(\bar Q),\quad \pi_S^*=0,\quad q^*=\frac{Y}{2k},\quad w^*=\frac{Y^2}{4k},\quad p^*=\begin{cases}Y\theta_H/(2k)&\alpha=\alpha_g\\ Y\theta_L/(2k)&\alpha=\alpha_b\end{cases},\quad I^*=\alpha_g,
--   $$
--   with $\alpha_g$ units received in the good market and $\alpha_g+\bar Q$ in the bad one;
--   2. **opportunistic targeting with overstock**, possible only when $V_{OS}(\bar Q)\le V_{OO}$:
--   $$
--   \pi_R^*=V_{OO},\quad \pi_S^*=\frac{\rho(1-\rho)[\alpha_g+(1-\rho)\bar Q]X^2}{4k},\quad q^*=\frac{(1-\rho)X}{2k},\quad w^*=\frac{(1-\rho)X^2}{4k},\quad p^*=\begin{cases}(1-\rho)X\theta_H/(2k)&\alpha=\alpha_g\\ (1-\rho)X\theta_L/(2k)&\alpha=\alpha_b\end{cases},\quad I^*=1-\bar Q,
--   $$
--   with $\alpha_g$ units received in the good market and $1$ in the bad one.
--
--   So the equilibrium is the column that gives the retailer the higher profit. In both, the retailer targets only the high-valuation consumers in the good market and everybody in the bad market; they differ in whether the supplier holds only the risk-free inventory (stockout in the bad market) or enough to cover it (overstock in the good market).
--
--   Differences from the source:
--   - correction: the paper's assumptions ($\alpha_b<\theta_L/\theta_H<\alpha_g$, footnote 1) and the range $(\theta_H/\theta_L)\alpha_b-\alpha_g<\bar Q\le 1-\alpha_g$ → the domain Focus ∧ HighOnlyDominated and $0\le\bar Q\le 1-\alpha_g$; reason: at $(\theta_H,\theta_L,\alpha_g,\alpha_b,\rho,k)=(1.739,1,0.801,0.304,0.128,1)$, which satisfies all of the paper's assumptions, a brute-force solution of the game at $\bar Q=0$ gives the retailer $\approx 0.2540$ (threshold inventory near $0.997$ at $w\approx 1.04kq^2$), above both columns ($V_{OO}\approx 0.2468$, $V_{OS}(0)\approx 0.2399$); the printed range's lower end is negative on the domain.
--   - correction: footnote 4's assumption $\alpha_g\le(\theta_H/\theta_L)\alpha_b$ "for the presented analysis" (p.14) → its other case $\alpha_g>(\theta_H/\theta_L)\alpha_b$, implied by Focus; reason: footnote 1 at the equilibrium quality has right side $\to 0$ as $\bar Q\downarrow(\theta_H/\theta_L)\alpha_b-\alpha_g$, so it holds across the medium range only in that other case, for which footnote 4 says the results "hold qualitatively the same"; and under $\alpha_g\le(\theta_H/\theta_L)\alpha_b$ one has $\theta_L^2<\alpha_b\theta_H^2$, so by Cauchy–Schwarz both table columns and Table C pay less than targeting only high-valuation consumers at $w=kq^2$, which is feasible once $\bar Q\ge\alpha_g-\alpha_b$.
--   - reading: "the unique equilibrium" → either column at a tie $V_{OS}(\bar Q)=V_{OO}$; reason: at a tie both columns give the retailer the same profit and the paper's rule "the case with the higher profit" does not decide.
--   - encoding: the printed orders $Q^*=\alpha_g$, $1$ → the units received $\alpha_g$ and $\alpha_g+\bar Q$ (stockout) or $\alpha_g$ and $1$ (overstock); reason: any order at least the deliverable quantity is optimal, so the order is not unique while the units received are.
--   - encoding: the contracts $w=kq^2+\varepsilon$, $kq^2/(1-\rho)+\varepsilon$ with $\varepsilon\to 0$ → subgame-perfect equilibria with $w^*=kq^{*2}$ and $kq^{*2}/(1-\rho)$ exactly; reason: the paper sets $\varepsilon=0$ in the results (OA p.7, fn 3); subgame perfection resolves the supplier's tie.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), §4 (B), Table B, pp.17–18 (PDF 17–18); Online Appendix §I.2 (B1)–(B3), OA pp.6–17 (PDF 51–62)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms

namespace ReactiveCapacity

/-- Table B: the equilibrium under medium reactive capacity. Jiang–Tian, *Effects of Reactive
Capacity*, SSRN 3308215 (version of May 5, 2022), §4 (B), Table B, pp.17–18 (PDF 17–18); proof in
Online Appendix §I.2 (B1)–(B3), OA pp.6–17.

On the domain `Dom` and for `0 ≤ Q̄ ≤ 1 − α_g`, an equilibrium exists, and every equilibrium outcome
is one of Table B's two columns, the one with the larger retailer profit (either one at a tie). With
`Y = Y(α_g + Q̄)` and `X = Y(1)`:

1. opportunistic targeting with stockout (`V_OS(Q̄) ≥ V_OO`): `π*_R = V_OS(Q̄)`, `π*_S = 0`,
   `q* = Y/(2k)`, `w* = Y²/(4k)`, `p* = Yθ_H/(2k)` in the good and `Yθ_L/(2k)` in the bad market,
   `I* = α_g`, and the retailer receives `α_g` and `α_g + Q̄`;
2. opportunistic targeting with overstock (`V_OS(Q̄) ≤ V_OO`): `π*_R = V_OO`,
   `π*_S = ρ(1 − ρ)[α_g + (1 − ρ)Q̄]X²/(4k)`, `q* = (1 − ρ)X/(2k)`, `w* = (1 − ρ)X²/(4k)`,
   `p* = (1 − ρ)Xθ_H/(2k)` and `(1 − ρ)Xθ_L/(2k)`, `I* = 1 − Q̄`, and the retailer receives `α_g`
   and `1`.

**Formalization Note** The table's `Q*` (`α_g`, `1`) is the printed order; any order at least the
deliverable quantity is optimal, so the statement records the units received. The printed range
`(θ_H/θ_L)α_b − α_g < Q̄` holds automatically on `Dom`. -/
theorem table_B (P : Params) (hP : P.Dom) (Qbar : ℝ) (h0 : 0 ≤ Qbar) (h1 : Qbar ≤ 1 - P.αg) :
    (∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    ∀ e : Outcome, IsEquilibrium P Qbar e →
      (P.V_OO ≤ P.V_OS Qbar ∧ e.πR = P.V_OS Qbar ∧ e.πS = 0 ∧
        e.q = P.Y (P.αg + Qbar) / (2 * P.k) ∧ e.w = P.Y (P.αg + Qbar) ^ 2 / (4 * P.k) ∧
        e.p .good = P.Y (P.αg + Qbar) * P.θH / (2 * P.k) ∧
        e.p .bad = P.Y (P.αg + Qbar) * P.θL / (2 * P.k) ∧
        e.I = P.αg ∧ e.R .good = P.αg ∧ e.R .bad = P.αg + Qbar) ∨
      (P.V_OS Qbar ≤ P.V_OO ∧ e.πR = P.V_OO ∧
        e.πS = P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) ∧
        e.q = (1 - P.ρ) * P.X / (2 * P.k) ∧ e.w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
        e.p .good = (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
        e.p .bad = (1 - P.ρ) * P.X * P.θL / (2 * P.k) ∧
        e.I = 1 - Qbar ∧ e.R .good = P.αg ∧ e.R .bad = 1) := by sorry

end ReactiveCapacity
