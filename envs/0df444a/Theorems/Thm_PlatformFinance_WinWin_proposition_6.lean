-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_6
-- name    : PlatformFinance.WinWin.proposition_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:30.599997+00:00
-- url     : https://prove2.me/theorems/90fd4922-da79-45ad-a79c-0e11a19da957
-- title:
--   Proposition 6, p. 18 — r̂₁(δ) ≤ r̂₂(δ); platform financing is win-win if r < r̂₁, lose-win if r̂₁ < r < r̂₂, lose-lose if r > r̂₂
-- statement:
--   A supplier with unit cost $c>0$ sells to a capital-constrained third-party seller on a platform that keeps the share $\varphi$ of revenue. The market size is uniform on $[a-\delta,a+\delta]$ and the price is $\tilde a-q$. The seller can be financed either by **trade credit** (she pays the supplier's deferred price $w$ after sales, with limited liability) or by a **platform loan** at rate $r$ (the supplier is paid $w$ upfront; she repays $w(1+r)$ to the platform after sales, with limited liability). Supplier and platform have capital cost $r_f$. Assume $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$, $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$.
--
--   Let $\Pi^T_s,\Pi^T_m$ be the seller's and the supplier's equilibrium expected profits in any subgame-perfect equilibrium of the trade-credit game, and $\Pi^P_s,\Pi^P_m$ those in any subgame-perfect equilibrium of the platform-financing game at rate $r$. With the thresholds $\hat r_1(\delta)$ (p. 15) and $\hat r_2(\delta)$ (p. 18):
--   1. $\hat r_1(\delta)\le\hat r_2(\delta)$;
--   2. **win-win:** if $r<\hat r_1(\delta)$, then $\Pi^P_s>\Pi^T_s$ and $\Pi^P_m>\Pi^T_m$;
--   3. **lose-win:** if $\hat r_1(\delta)<r<\hat r_2(\delta)$, then $\Pi^P_s\le\Pi^T_s$ and $\Pi^P_m>\Pi^T_m$;
--   4. **lose-lose:** if $r>\hat r_2(\delta)$, then $\Pi^P_s\le\Pi^T_s$ and $\Pi^P_m\le\Pi^T_m$.
--
--   So a platform loan never benefits the seller without also benefiting the supplier: the outcome in which the seller wins and the supplier loses does not occur.
--
--   **Formalization Note.** "Win" is strict improvement under platform financing and "lose" is weak worsening, the reading Propositions 4 and 5 give. The thresholds use the corrected $r_3$ (with $8c\delta$, p. 38). The hypothesis $\delta<a$ formalizes the standing assumption that the smallest market size keeps the price positive (p. 8); the comparison $\hat r_1\le\hat r_2$ fails for some $\delta>a$. Equilibria include the seller's and the least-price supplier tie-breaks described in the model file.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 18, Proposition 6; proof pp. 40–41

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_6 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    rhat1 a δ φ c rf ≤ rhat2 a δ φ c rf ∧
      (r < rhat1 a δ φ c rf →
        sellerProfitT a δ φ σT < sellerProfitP a δ φ r σP ∧
          supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat1 a δ φ c rf < r → r < rhat2 a δ φ c rf →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT ∧
          supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat2 a δ φ c rf < r →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT ∧
          supplierProfitP c rf σP ≤ supplierProfitT a δ φ c rf σT) := by sorry
end PlatformFinance.WinWin
