-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_profits_T
-- name    : PlatformFinance.WinWin.profits_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.761984+00:00
-- url     : https://prove2.me/theorems/6261dd10-fafb-4d92-8e5d-8badc731a541
-- title:
--   Proof of Proposition 1, pp. 32–33 — equilibrium profits of seller and supplier under trade credit
-- statement:
--   In the setting of Proposition 1 (trade credit, $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$), write $K_0=(1-\varphi)a-c(1+r_f)$, $S$ and $\delta_1$ as in Proposition 1, and
--   $$K=2\sqrt{\frac{\big((\delta+3a)(1-\varphi)-3c(1+r_f)\big)^3}{\delta(1-\varphi)}}-(9a+2\delta)(1-\varphi)+9c(1+r_f).$$
--   In every subgame-perfect equilibrium the seller's and the supplier's expected profits on the equilibrium path are
--   $$\Pi^T_s=\begin{cases}\dfrac{K_0^2}{16(1-\varphi)}&\delta\le\delta_1,\\[2mm]\dfrac{1}{27}\delta^2(1-\varphi)(S-1)^3&\delta>\delta_1,\end{cases}\qquad \Pi^T_m=\begin{cases}\dfrac{K_0^2}{8(1-\varphi)}&\delta\le\delta_1,\\[2mm]\dfrac{\delta K}{27}&\delta>\delta_1.\end{cases}$$
--
--   These are the trade-credit profits that Propositions 4–6 compare with platform financing.
--
--   **Formalization Note.** The $\delta>\delta_1$ branch of $\Pi^T_m$ is corrected. Pages 33 and 38 print $\frac{\delta}{27}\big(((2\delta-6a)(1-\varphi)+6c(1+r_f))S+(9a-2\delta)(1-\varphi)-9c(1+r_f)\big)$, which is negative on typical data; the supplier's equilibrium profit is $\delta^2(1-\varphi)(S-1)^2(2S+1)/27=\delta K/27$, with the $K$ that p. 38 itself defines (the printed signs of the $a$ and $c$ terms are flipped).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, pp. 32–33, proof of Proposition 1, displays Π^T_s (p. 32) and Π^T_m (p. 33); K on p. 38

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem profits_T (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (σ : Profile) (hσ : IsSPET a δ φ c rf σ) :
    sellerProfitT a δ φ σ =
        (if δ ≤ delta1 a φ c rf then K0 a φ c rf ^ 2 / (16 * (1 - φ))
         else δ ^ 2 * (1 - φ) * (Sroot a δ φ c rf - 1) ^ 3 / 27) ∧
      supplierProfitT a δ φ c rf σ =
        (if δ ≤ delta1 a φ c rf then K0 a φ c rf ^ 2 / (8 * (1 - φ))
         else δ * Kfun a δ φ c rf / 27) := by sorry
end PlatformFinance.WinWin
