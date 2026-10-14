-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_proposition_1
-- name    : PlatformFinance.PlatformProfit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:39.481305+00:00
-- url     : https://prove2.me/theorems/a6b9b8b1-dec0-4ac0-a7a1-9f0adc557bd0
-- title:
--   Proposition 1, p. 11 — the trade-credit game has an equilibrium, and every equilibrium has price w^T and order q^T
-- statement:
--   Consider the trade-credit game: the supplier (unit cost $c>0$, capital cost $r_f\ge 0$) sets a deferred wholesale price $w$, the seller then orders $q\ge 0$, the market size $\tilde a$ is uniform on $[a-\delta,a+\delta]$ and the price is $\tilde a-q$; the platform keeps the share $\varphi\in[0,1)$ of the revenue. Assume $0<\delta<a$ and $(1-\varphi)a>c(1+r_f)$. Let
--   $$
--   \delta_1=\frac{(5\sqrt{10}-14)((1-\varphi)a-c(1+r_f))}{8(1-\varphi)},\qquad S=\sqrt{\frac{(\delta+3a)(1-\varphi)-3c(1+r_f)}{\delta(1-\varphi)}} .
--   $$
--   Then the game has a subgame-perfect equilibrium, and in every subgame-perfect equilibrium the wholesale price and the seller's order are
--   $$
--   w^T=\begin{cases}\dfrac{(1-\varphi)a+c(1+r_f)}{2} & \delta\le\delta_1,\\[2mm] (1-\varphi)\big(a-\delta(S-2)\big) & \delta>\delta_1,\end{cases}\qquad
--   q^T=\begin{cases}\dfrac{(1-\varphi)a-c(1+r_f)}{4(1-\varphi)} & \delta\le\delta_1,\\[2mm] \dfrac{\delta}{3}(S-1) & \delta>\delta_1.\end{cases}
--   $$
--
--   Below $\delta_1$ the supplier prices so that the seller never defaults; above it he raises the price and accepts default risk. The closed form is the input to every comparison between trade credit and platform financing.
--
--   **Formalization Note** The page's $\delta>\delta_1$ branch prints $\sqrt{(\delta+3a)-3c(1+r_f)/(1-\varphi)}$, which drops a factor $\delta$; the statement uses the form of the proof (p. 31, $w_2$) and of (3) (p. 36). Equilibria use two tie-breaks: an indifferent seller orders zero, and the supplier's price is the least optimal one, which places $\delta=\delta_1$ in the low-price branch as the page does. $0<\delta<a$ reads the page's assumption that the price is always positive; $\varphi<1$, $c>0$ and $r_f\ge0$ are the readings of $\varphi\in[0,1]$, of a production cost and of a risk-free rate. Existence is part of the statement so that "every equilibrium" is not vacuous.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 11, Proposition 1; proof pp. 31–33

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- Proposition 1 (p. 11): the trade-credit game has a subgame-perfect equilibrium, and in every
one the wholesale price is `w^T` and the seller's order is `q^T`. -/
theorem proposition_1 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a) :
    (∃ σ : PlatformFinance.WinWin.Profile, PlatformFinance.WinWin.IsSPET a δ φ c rf σ) ∧
      ∀ σ : PlatformFinance.WinWin.Profile, PlatformFinance.WinWin.IsSPET a δ φ c rf σ →
        σ.w = wT a δ φ c rf ∧ σ.order σ.w = qT a δ φ c rf := by sorry

end PlatformFinance.PlatformProfit
