-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_proposition_7
-- name    : PlatformFinance.PlatformProfit.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:47.539027+00:00
-- url     : https://prove2.me/theorems/cc6a9f47-8d60-4374-9f79-9603a3df8632
-- title:
--   Proposition 7, p. 19 — for δ ≤ δ₂ the platform gains from platform financing at r_f < r < r₅ when c ≤ a(1−φ)²/(1+r_f), and at r₆ < r < r_f otherwise
-- statement:
--   A seller without capital buys $q$ units from a supplier with unit cost $c>0$ and sells them on a platform at the price $\tilde a-q$, where the market size $\tilde a$ is uniform on $[a-\delta,a+\delta]$ with $0<\delta<a$; the platform keeps the share $\varphi\in[0,1)$ of the revenue, the supplier's and the platform's capital cost is $r_f\ge0$, and $(1-\varphi)a>c(1+r_f)$. Compare two schemes: **trade credit**, where the supplier defers payment and bears the default risk, and **platform financing** at loan rate $r$, where the platform lends the purchase cost and bears the default risk. Let $\Pi^T_p$ be the platform's profit in a subgame-perfect equilibrium of the trade-credit game and $\Pi^P_p(r)$ its profit in a subgame-perfect equilibrium of the platform-financing game at rate $r$ (one equilibrium for every admissible $r$). Let
--   $$
--   \delta_2=\frac{(1-\varphi)a-c(1+r_f)}{(2+\sqrt6)(1-\varphi)},\qquad r_1=\frac{(1-\varphi)(a-(\sqrt6+2)\delta)}{c}-1,
--   $$
--   $$
--   r_6=\frac{\sqrt{8a^2(2-\varphi)(1-\varphi)^3+\varphi^2\big(2a(1-\varphi)+c(1+r_f)\big)^2}-2a(1-\varphi)\varphi-c(4+r_f\varphi-\varphi)}{2c(2-\varphi)},\qquad r_5=\min\{r_1,r_6\}.
--   $$
--   Suppose $\delta\le\delta_2$. Then:
--
--   1. if $c\le\dfrac{a(1-\varphi)^2}{1+r_f}$, then $r_6\ge r_f$, and $\Pi^P_p(r)>\Pi^T_p$ for every $r$ with $r_f<r<r_5$;
--   2. if $c>\dfrac{a(1-\varphi)^2}{1+r_f}$, then $r_6<r_f$, and $\Pi^P_p(r)>\Pi^T_p$ for every $r>-1$ with $r_6<r<r_f$.
--
--   At low market uncertainty the platform therefore profits from lending slightly above its own capital cost when production is cheap, and slightly below it when production is expensive; in the second case platform financing can benefit all three parties.
--
--   **Formalization Note** The page states that "there exist two thresholds $r_5$ and $r_6$"; read literally this holds with an empty interval. The statement uses the explicit thresholds of the proof (p. 41) together with the proof's facts $r_6\ge r_f$ (low cost) and $r_6<r_f$ (high cost), which is stronger than the page. The rate condition $r>-1$ in the second clause is condition (iii) of the Appendix (p. 36). The proof writes $\delta<\delta_2$; the statement's $\delta\le\delta_2$ is used. Equilibria carry the model's tie-breaks; the platform-financing equilibria are a family indexed by the rate, required to be equilibria at every $r$ satisfying conditions (ii)–(iii).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 19, Proposition 7; proof p. 41 (r₅, r₆)

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- Proposition 7 (p. 19), with the thresholds `r₅ = min{r₁, r₆}` and `r₆` of its proof (p. 41):
for `δ ≤ δ₂`, if `c ≤ a(1 − φ)²/(1 + r_f)` then `r_f ≤ r₆` and the platform strictly prefers
platform financing at every rate `r_f < r < r₅`; if `c > a(1 − φ)²/(1 + r_f)` then `r₆ < r_f` and
it strictly prefers platform financing at every rate `r₆ < r < r_f` (with `r > −1`). -/
theorem proposition_7 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ2 : δ ≤ delta2 a φ c rf)
    (σT : PlatformFinance.WinWin.Profile) (hT : PlatformFinance.WinWin.IsSPET a δ φ c rf σT)
    (σP : ℝ → PlatformFinance.WinWin.Profile)
    (hP : ∀ r : ℝ, -1 < r → c * (1 + r) < (a + δ) * (1 - φ) → PlatformFinance.WinWin.IsSPEP a δ φ c rf r (σP r)) :
    (c ≤ cbar a φ rf →
        rf ≤ r6 a φ c rf ∧
          ∀ r : ℝ, rf < r → r < r5 a δ φ c rf →
            platformProfitT a δ φ σT < platformProfitP a δ φ rf r (σP r)) ∧
      (cbar a φ rf < c →
        r6 a φ c rf < rf ∧
          ∀ r : ℝ, -1 < r → r6 a φ c rf < r → r < rf →
            platformProfitT a δ φ σT < platformProfitP a δ φ rf r (σP r)) := by sorry

end PlatformFinance.PlatformProfit
