-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_profits_P
-- name    : PlatformFinance.WinWin.profits_P
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.44985+00:00
-- url     : https://prove2.me/theorems/8abf02c2-c918-43d2-9e47-79bff1bc8654
-- title:
--   Proof of Proposition 2, p. 35 — equilibrium profits of seller and supplier under platform financing
-- statement:
--   In the setting of Proposition 2 (platform financing at rate $r$, with the standing conditions, $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$), in every subgame-perfect equilibrium the seller's and the supplier's expected profits on the equilibrium path are
--   $$\Pi^P_s=\begin{cases}\dfrac{(a(1-\varphi)-c(1+r))^2}{16(1-\varphi)}&\delta\le\delta_r,\\[2mm]\dfrac{((a+\delta)(1-\varphi)-c(1+r))^3}{216\,\delta(1-\varphi)^2}&\delta>\delta_r,\end{cases}$$
--   $$\Pi^P_m=\begin{cases}\dfrac{(1+r_f)(a(1-\varphi)-c(1+r))^2}{8(r+1)(1-\varphi)}&\delta\le\delta_r,\\[2mm]\dfrac{(1+r_f)((a+\delta)(1-\varphi)-c(1+r))^2}{12(1+r)(1-\varphi)}&\delta>\delta_r.\end{cases}$$
--
--   These are the platform-financing profits that Propositions 4–6 compare with trade credit.
--
--   **Formalization Note.** The page introduces these as "the equilibrium profits under trade credit"; they are the platform-financing profits (the display's superscript is $P$).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 35, proof of Proposition 2, displays Π^P_s and Π^P_m

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem profits_P (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σ : Profile) (hσ : IsSPEP a δ φ c rf r σ) :
    sellerProfitP a δ φ r σ =
        (if δ ≤ deltaR a φ c r then (a * (1 - φ) - c * (1 + r)) ^ 2 / (16 * (1 - φ))
         else ((a + δ) * (1 - φ) - c * (1 + r)) ^ 3 / (216 * δ * (1 - φ) ^ 2)) ∧
      supplierProfitP c rf σ =
        (if δ ≤ deltaR a φ c r then
          (1 + rf) * (a * (1 - φ) - c * (1 + r)) ^ 2 / (8 * (r + 1) * (1 - φ))
         else (1 + rf) * ((a + δ) * (1 - φ) - c * (1 + r)) ^ 2 / (12 * (1 + r) * (1 - φ))) := by sorry
end PlatformFinance.WinWin
