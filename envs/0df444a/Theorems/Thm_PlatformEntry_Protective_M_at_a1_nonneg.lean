-- Prove2me | Theorems.Thm_PlatformEntry_Protective_M_at_a1_nonneg
-- name    : PlatformEntry.Protective.M_at_a1_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:17.975793+00:00
-- url     : https://prove2.me/theorems/339a3a6d-96fa-4cf2-bea6-c6eea43738fd
-- title:
--   Proof of Proposition 3, PDF p. 36 — M(a₁) ≥ 0 at the threshold a₁ + e^B_N(a₁) = Δ
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy (5) and $H\le 1/4$, and let $c_S>1/2$, $K>0$. Let $\underline a_1$ be a base value with $\underline a_1+e^B_N(\underline a_1)=\Delta$. Then
--   $$M(\underline a_1)=\Pi^S_N(\Delta-\underline a_1)-\Pi^S_E\big(e^B_E(\underline a_1)\big)\ge 0 .$$
--
--   At the lower threshold the cutoff effort coincides with the non-entry first-best, and non-entry profits dominate entry profits in the protective regime. This is the starting point for the definition of $\bar a_1$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Proof of Proposition 3, PDF p. 36: M(a₁) ≥ 0 at the threshold a₁ defined by
a₁ + e^B_N(a₁) = Δ. -/
theorem M_at_a1_nonneg (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS) (hK : 0 < K)
    (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) (a₁ : ℝ)
    (ha₁ : a₁ + eBN f cS a₁ = Delta δ f β K) :
    0 ≤ Mfun δ f β cS K a₁ := by sorry

end PlatformEntry.Protective
