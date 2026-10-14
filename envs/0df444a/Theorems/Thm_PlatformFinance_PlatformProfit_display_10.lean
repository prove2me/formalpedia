-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_display_10
-- name    : PlatformFinance.PlatformProfit.display_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:48.39553+00:00
-- url     : https://prove2.me/theorems/9054c85d-80fa-468d-8e68-e9ea957fdb9b
-- title:
--   (10), p. 41 — for δ ≤ δ_r the platform's equilibrium profit under platform financing at rate r in closed form
-- statement:
--   In the platform-financing game of Proposition 2 at loan rate $r$ (with $r>-1$, $c(1+r)<(a+\delta)(1-\varphi)$, $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$), let $\delta\le\delta_r=\frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}$. Then in every subgame-perfect equilibrium the platform's expected profit
--   $\Pi^P_p=\mathbb E\big[\varphi(\tilde a-q^P)q^P+\min\{(1-\varphi)(\tilde a-q^P)q^P,\,w^Pq^P(1+r)\}-w^Pq^P(1+r_f)\big]$ equals
--   $$
--   \Pi^P_p=\frac{\big(a(1-\varphi)-c(1+r)\big)\Big(a(1-\varphi)\big(r(\varphi+2)-2r_f(1-\varphi)+3\varphi\big)-c(r+1)\big(r(\varphi-2)+2r_f(1-\varphi)-\varphi\big)\Big)}{16(r+1)(1-\varphi)^2}.
--   $$
--
--   This is the platform-financing side of the comparison in Proposition 7.
--
--   **Formalization Note** $\Pi^P_p$ is evaluated along the equilibrium path of an arbitrary subgame-perfect equilibrium of the platform-financing game at rate $r$.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 41, (10) (proof of Proposition 7); also p. 35, first branch of Π^P_p

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- (10) (p. 41; first branch of `Π^P_p`, p. 35): for `δ ≤ δ_r`, the platform's equilibrium
profit under platform financing at rate `r` is the closed form (10). -/
theorem display_10 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (hδr : δ ≤ deltaR a φ c r) (σ : PlatformFinance.WinWin.Profile) (hσ : PlatformFinance.WinWin.IsSPEP a δ φ c rf r σ) :
    platformProfitP a δ φ rf r σ =
      (a * (1 - φ) - c * (1 + r)) *
          (a * (1 - φ) * (r * (φ + 2) - 2 * rf * (1 - φ) + 3 * φ) -
            c * (r + 1) * (r * (φ - 2) + 2 * rf * (1 - φ) - φ)) /
        (16 * (r + 1) * (1 - φ) ^ 2) := by sorry

end PlatformFinance.PlatformProfit
