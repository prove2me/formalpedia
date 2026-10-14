-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_proposition_2
-- name    : PlatformFinance.PlatformProfit.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:40.125104+00:00
-- url     : https://prove2.me/theorems/c883fead-52d2-4ccb-93f7-148eb18482e6
-- title:
--   Proposition 2, p. 13 — the platform-financing game at rate r has an equilibrium, and every equilibrium has price w^P and order q^P
-- statement:
--   Consider the platform-financing game at loan rate $r$: the supplier (unit cost $c>0$, capital cost $r_f\ge0$) sets an upfront wholesale price $w$, the seller then orders $q\ge0$ with a loan $wq$ from the platform at rate $r$, the market size $\tilde a$ is uniform on $[a-\delta,a+\delta]$ and the price is $\tilde a-q$; the platform keeps the share $\varphi\in[0,1)$ of the revenue. Assume $0<\delta<a$, $(1-\varphi)a>c(1+r_f)$, $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$. Let $\delta_r=\frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}$. Then the game has a subgame-perfect equilibrium, and in every one
--   $$
--   w^P=\begin{cases}\dfrac{(1-\varphi)a+c(1+r)}{2(1+r)} & \delta\le\delta_r,\\[2mm] \dfrac{(1-\varphi)(a+\delta)+c(1+r)}{2(1+r)} & \delta>\delta_r,\end{cases}\qquad
--   q^P=\begin{cases}\dfrac{(1-\varphi)a-c(1+r)}{4(1-\varphi)} & \delta\le\delta_r,\\[2mm] \dfrac{(1-\varphi)(a+\delta)-c(1+r)}{6(1-\varphi)} & \delta>\delta_r.\end{cases}
--   $$
--
--   Together with Proposition 1 this gives the two equilibria that §4.3 compares.
--
--   **Formalization Note** $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$ are conditions (iii) and (ii) of the Appendix (p. 36). The tie-breaks are those of the model; the least-price convention places $\delta=\delta_r$ in the first branch, as the page does. Existence is part of the statement.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Proposition 2; proof pp. 33–35; conditions (ii)–(iii), p. 36

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- Proposition 2 (p. 13): at an interest rate `r` with `−1 < r` and
`c(1 + r) < (a + δ)(1 − φ)`, the platform-financing game has a subgame-perfect equilibrium, and in
every one the wholesale price is `w^P` and the seller's order is `q^P`. -/
theorem proposition_2 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ)) :
    (∃ σ : PlatformFinance.WinWin.Profile, PlatformFinance.WinWin.IsSPEP a δ φ c rf r σ) ∧
      ∀ σ : PlatformFinance.WinWin.Profile, PlatformFinance.WinWin.IsSPEP a δ φ c rf r σ →
        σ.w = wP a δ φ c r ∧ σ.order σ.w = qP a δ φ c r := by sorry

end PlatformFinance.PlatformProfit
