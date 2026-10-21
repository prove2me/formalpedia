-- Prove2me | Theorems.Thm_PlatformEntry_Protective_case_1_1
-- name    : PlatformEntry.Protective.case_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:24.959646+00:00
-- url     : https://prove2.me/theorems/83c3f32e-a79d-4b2a-b934-e06e97e07ad8
-- title:
--   Case 1.1 of the proof of Proposition 3, PDF p. 36 — for a ≤ a₁ the effort e^B_N(a) is optimal
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy (5) and $H\le 1/4$, let $c_S>1/2$, $K>0$, and let $\underline a_1+e^B_N(\underline a_1)=\Delta$. Then for every base value $a\le\underline a_1$ the effort $e^B_N(a)$ maximizes the seller's total profit
--   $$\Pi^S(e_S)=\begin{cases}\Pi^S_N(e_S)&e_S+a\le\Delta\\ \Pi^S_E(e_S)&e_S+a>\Delta\end{cases}$$
--   over all $e_S\in\mathbb R$.
--
--   For low base values the seller's first-best effort already keeps the product below the entry threshold, so she has no reason to distort it and the platform stays out.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, Case 1.1, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Case 1.1 of the proof of Proposition 3, PDF p. 36: for a ≤ a₁ the first-best effort
e^B_N(a) is optimal. -/
theorem case_1_1 (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS) (hK : 0 < K)
    (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) (a₁ : ℝ)
    (ha₁ : a₁ + eBN f cS a₁ = Delta δ f β K) :
    ∀ a : ℝ, a ≤ a₁ → IsOptimalEffort δ f β cS K a (eBN f cS a) := by sorry

end PlatformEntry.Protective
