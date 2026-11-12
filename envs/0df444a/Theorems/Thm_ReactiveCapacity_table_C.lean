-- Prove2me | Theorems.Thm_ReactiveCapacity_table_C
-- name    : ReactiveCapacity.table_C
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:19:05.551381+00:00
-- url     : https://prove2.me/theorems/bf97c30c-79c4-4a1f-ad99-e9a8c5eacf40
-- title:
--   Table C: under high reactive capacity the equilibrium is opportunistic targeting without stockout or overstock (corrected: domain)
-- statement:
--   Assume the standing assumptions, the focus condition and high-only dominance, and let $\bar Q\ge 1-\alpha_g$. With $X=Y(1)$, an equilibrium exists and every equilibrium outcome is
--   $$
--   \pi_R^*=\frac{X^2(\rho\alpha_g+1-\rho)}{4k},\quad \pi_S^*=0,\quad q^*=\frac{X}{2k},\quad w^*=\frac{X^2}{4k},\quad p^*=\begin{cases}X\theta_H/(2k)&\alpha=\alpha_g\\ X\theta_L/(2k)&\alpha=\alpha_b\end{cases},\quad I^*\in\bigl[\max\{0,1-\bar Q\},\alpha_g\bigr],
--   $$
--   with $\alpha_g$ units received in the good market and $1$ in the bad one.
--
--   With enough reactive capacity the supplier bears no inventory risk, the retailer pays only the marginal cost, and the outcome no longer depends on $\bar Q$.
--
--   Differences from the source:
--   - correction: the paper's assumptions ($\alpha_b<\theta_L/\theta_H<\alpha_g$, footnote 1) → the domain Focus ∧ HighOnlyDominated; reason: at $(4,1,19/20,1/50,1/10,1)$, which satisfies all of the paper's assumptions, at $\bar Q=1$ the retailer gets $\approx 0.452$ by targeting only high-valuation consumers ($q=\theta_H/(2k)=2$), above Table C's $0.4117$ ($q=0.6432$).
--   - correction: footnote 4's assumption $\alpha_g\le(\theta_H/\theta_L)\alpha_b$ "for the presented analysis" (p.14) → its other case $\alpha_g>(\theta_H/\theta_L)\alpha_b$, implied by Focus; reason: footnote 1 at the equilibrium quality has right side $\to 0$ as $\bar Q\downarrow(\theta_H/\theta_L)\alpha_b-\alpha_g$, so it holds across the medium range only in that other case, for which footnote 4 says the results "hold qualitatively the same"; and under $\alpha_g\le(\theta_H/\theta_L)\alpha_b$ one has $\theta_L^2<\alpha_b\theta_H^2$, so by Cauchy–Schwarz both table columns and Table C pay less than targeting only high-valuation consumers at $w=kq^2$, which is feasible once $\bar Q\ge\alpha_g-\alpha_b$.
--   - generalization: $\bar Q>1-\alpha_g$ → $\bar Q\ge 1-\alpha_g$; reason: at $\bar Q=1-\alpha_g$ Table B's stockout column has $S=1$ and coincides with Table C.
--   - encoding: $I^*\in[1-\bar Q,\alpha_g]$ → $I^*\in[\max\{0,1-\bar Q\},\alpha_g]$; reason: inventories are nonnegative, which matters only for $\bar Q>1$.
--   - encoding: the printed orders $Q^*=\alpha_g$, $1$ and $w=kq^2+\varepsilon$ → the units received, and subgame-perfect equilibria with $w^*=kq^{*2}$; reason: any order at least the deliverable quantity is optimal; the paper sets $\varepsilon=0$ in the results (OA p.7, fn 3).
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), §4 (C), Table C, pp.19–20 (PDF 19–20); Online Appendix §I.2 (C1)–(C2), OA pp.18–20 (PDF 63–65)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms

namespace ReactiveCapacity

/-- Table C: the equilibrium under high reactive capacity. Jiang–Tian, *Effects of Reactive
Capacity*, SSRN 3308215 (version of May 5, 2022), §4 (C), Table C, pp.19–20 (PDF 19–20); proof in
Online Appendix §I.2 (C1)–(C2), OA pp.18–20.

On the domain `Dom` and for `Q̄ ≥ 1 − α_g`, an equilibrium exists, and every equilibrium outcome is
opportunistic targeting without stockout or overstock: with `X = Y(1)`,
`π*_R = X²(ρα_g + 1 − ρ)/(4k)`, `π*_S = 0`, `q* = X/(2k)`, `w* = X²/(4k)`, `p* = Xθ_H/(2k)` in the
good and `Xθ_L/(2k)` in the bad market, `I* ∈ [max(0, 1 − Q̄), α_g]`, and the retailer receives
`α_g` and `1`.

**Formalization Note** The statement includes `Q̄ = 1 − α_g`, where Table B gives the same outcome.
`max(0, ·)` covers `Q̄ > 1`. The table's `Q*` is recorded as the units received. -/
theorem table_C (P : Params) (hP : P.Dom) (Qbar : ℝ) (h : 1 - P.αg ≤ Qbar) :
    (∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    ∀ e : Outcome, IsEquilibrium P Qbar e →
      e.πR = P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) ∧ e.πS = 0 ∧
      e.q = P.X / (2 * P.k) ∧ e.w = P.X ^ 2 / (4 * P.k) ∧
      e.p .good = P.X * P.θH / (2 * P.k) ∧ e.p .bad = P.X * P.θL / (2 * P.k) ∧
      max 0 (1 - Qbar) ≤ e.I ∧ e.I ≤ P.αg ∧ e.R .good = P.αg ∧ e.R .bad = 1 := by sorry

end ReactiveCapacity
