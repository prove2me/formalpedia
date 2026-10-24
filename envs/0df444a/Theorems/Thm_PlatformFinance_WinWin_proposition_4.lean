-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_4
-- name    : PlatformFinance.WinWin.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:28.114156+00:00
-- url     : https://prove2.me/theorems/23739921-9f58-4e4a-ac36-025d6e380c70
-- title:
--   Proposition 4, p. 18 — the seller prefers platform financing exactly when r < r̂₁(δ)
-- statement:
--   Under the standing conditions of Proposition 3, let $\Pi^T_s$ be the seller's equilibrium expected profit in any subgame-perfect equilibrium of the trade-credit game and $\Pi^P_s$ her equilibrium expected profit in any subgame-perfect equilibrium of the platform-financing game at rate $r$. Then
--   $$r<\hat r_1(\delta)\ \Longrightarrow\ \Pi^P_s>\Pi^T_s,\qquad r>\hat r_1(\delta)\ \Longrightarrow\ \Pi^P_s\le\Pi^T_s,$$
--   and also $\Pi^P_s\le\Pi^T_s$ at $r=\hat r_1(\delta)$ when $\delta\le\delta_2$ or $\delta>\delta_3$.
--
--   This is the seller's half of the win-win comparison of Proposition 6.
--
--   **Formalization Note.** The boundary rate $r=\hat r_1(\delta)$ belongs to the "otherwise" clause except for $\delta_2<\delta\le\delta_3$, where $r=r_1$ puts platform financing at $\delta=\delta_r$ in its no-default branch and $\Pi^P_s>\Pi^T_s$, contradicting the page (see Proposition 3).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 18, Proposition 4; proof p. 38

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_4 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    (r < rhat1 a δ φ c rf → sellerProfitT a δ φ σT < sellerProfitP a δ φ r σP) ∧
      (rhat1 a δ φ c rf < r ∨
          (r = rhat1 a δ φ c rf ∧ (δ ≤ delta2 a φ c rf ∨ delta3 a φ c rf < δ)) →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT) := by sorry
end PlatformFinance.WinWin
