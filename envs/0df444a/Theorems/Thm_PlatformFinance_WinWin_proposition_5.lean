-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_5
-- name    : PlatformFinance.WinWin.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.245731+00:00
-- url     : https://prove2.me/theorems/5658fd85-7376-4e8e-bea9-11baef623766
-- title:
--   Proposition 5, p. 18 — the supplier prefers platform financing exactly when r < r̂₂(δ)
-- statement:
--   Under the standing conditions of Proposition 3, let $\Pi^T_m$ be the supplier's equilibrium expected profit in any subgame-perfect equilibrium of the trade-credit game and $\Pi^P_m$ his equilibrium profit in any subgame-perfect equilibrium of the platform-financing game at rate $r$, and let $\hat r_2(\delta)$ be the threshold of p. 18 ($r_f$ for $\delta\le\delta_2$, $r_3$ for $\delta_2<\delta\le\delta_1$, $r_4$ for $\delta>\delta_1$, pp. 38–39). Then
--   $$r<\hat r_2(\delta)\ \Longrightarrow\ \Pi^P_m>\Pi^T_m,\qquad r\ge\hat r_2(\delta)\ \Longrightarrow\ \Pi^P_m\le\Pi^T_m.$$
--
--   **Formalization Note.** $r_3$ uses $(2ac+8c\delta)$ under the inner root, correcting the printed $(2ac+8\delta)$ on pp. 38–39: $r_3$ is the smaller root in $r$ of $2(1+r_f)((a+\delta)(1-\varphi)-c(1+r))^2=3(1+r)(a(1-\varphi)-c(1+r_f))^2$, the Case 2 difference on p. 39, and with the printed form the proposition fails at some parameter points.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 18, Proposition 5 (r̂₂ p. 18; r₃, K, r₄ pp. 38–39); proof pp. 38–39

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_5 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    (r < rhat2 a δ φ c rf → supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat2 a δ φ c rf ≤ r → supplierProfitP c rf σP ≤ supplierProfitT a δ φ c rf σT) := by sorry
end PlatformFinance.WinWin
