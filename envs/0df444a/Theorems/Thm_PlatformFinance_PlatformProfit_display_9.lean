-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_display_9
-- name    : PlatformFinance.PlatformProfit.display_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:31.306454+00:00
-- url     : https://prove2.me/theorems/55b501e8-6d03-4290-93fb-05a4d6494e4f
-- title:
--   (9), p. 41 — for δ ≤ δ₁ the platform's trade-credit equilibrium profit is φ(a(1−φ)−c(1+r_f))(3a(1−φ)+c(1+r_f))/(16(1−φ)²)
-- statement:
--   In the trade-credit game of Proposition 1 (market size $\tilde a$ uniform on $[a-\delta,a+\delta]$, platform share $\varphi\in[0,1)$, unit cost $c>0$, risk-free rate $r_f\ge0$, $0<\delta<a$, $(1-\varphi)a>c(1+r_f)$), let $\delta\le\delta_1=\frac{(5\sqrt{10}-14)((1-\varphi)a-c(1+r_f))}{8(1-\varphi)}$. Then in every subgame-perfect equilibrium the platform's expected profit $\Pi^T_p=\mathbb E[\varphi(\tilde a-q^T)q^T]$ is
--   $$
--   \Pi^T_p=\frac{\varphi\,\big(a(1-\varphi)-c(1+r_f)\big)\big(3a(1-\varphi)+c(1+r_f)\big)}{16(1-\varphi)^2}.
--   $$
--
--   This is the trade-credit side of the comparison in Proposition 7.
--
--   **Formalization Note** $\Pi^T_p$ is the expectation of the platform's commission at the equilibrium order, evaluated along the equilibrium path of an arbitrary subgame-perfect equilibrium (with the tie-breaks of the model).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 41, (9) (proof of Proposition 7); also p. 33, first branch of Π^T_p

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- (9) (p. 41; first branch of `Π^T_p`, p. 33): for `δ ≤ δ₁`, the platform's equilibrium
profit under trade credit is `φ(a(1 − φ) − c(1 + r_f))(3a(1 − φ) + c(1 + r_f))/(16(1 − φ)²)`. -/
theorem display_9 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ1 : δ ≤ delta1 a φ c rf) (σ : PlatformFinance.WinWin.Profile) (hσ : PlatformFinance.WinWin.IsSPET a δ φ c rf σ) :
    platformProfitT a δ φ σ =
      φ * (a * (1 - φ) - c * (1 + rf)) * (3 * a * (1 - φ) + c * (1 + rf)) /
        (16 * (1 - φ) ^ 2) := by sorry

end PlatformFinance.PlatformProfit
