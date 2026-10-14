-- Prove2me | Theorems.Thm_PlatformEntry_Protective_case_1_2
-- name    : PlatformEntry.Protective.case_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:30.15504+00:00
-- url     : https://prove2.me/theorems/05e61b7a-4f08-4bb9-847b-4d079d09bd29
-- title:
--   Case 1.2 of the proof of Proposition 3, PDF p. 36 — for a > a₁ with M(a) ≥ 0 the cutoff effort Δ − a is optimal
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy (5) and $H\le 1/4$, let $c_S>1/2$, $K>0$, and let $\underline a_1+e^B_N(\underline a_1)=\Delta$. Then for every base value $a>\underline a_1$ with
--   $$\Pi^S_N(\Delta-a)\ge\Pi^S_E\big(e^B_E(a)\big),\quad\text{i.e. } M(a)\ge 0,$$
--   the cutoff effort $e_S=\Delta-a$ maximizes the seller's total profit $\Pi^S$ over all $e_S\in\mathbb R$.
--
--   This is the underinvestment region: the seller chooses less than her first-best effort so that the product value stays exactly at the entry threshold and the platform does not enter.
--
--   **Formalization Note** In the paper the case is $a\in(\underline a_1,\bar a_1)$, and the proof uses $a<\bar a_1$ only through $\Pi^S_N(\Delta-a)\ge\Pi^S_E(e^B_E(a))$. The milestone takes that inequality as its hypothesis, so it does not depend on the definition of $\bar a_1$. Efforts range over all reals: $\Delta-a$ can be negative.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, Case 1.2, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Case 1.2 of the proof of Proposition 3, PDF p. 36: for a > a₁ with
Π^S_N(Δ − a) ≥ Π^S_E(e^B_E(a)) (i.e. M(a) ≥ 0, which is what a < ā₁ provides),
the cutoff effort Δ − a is optimal. -/
theorem case_1_2 (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS) (hK : 0 < K)
    (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) (a₁ : ℝ)
    (ha₁ : a₁ + eBN f cS a₁ = Delta δ f β K) :
    ∀ a : ℝ, a₁ < a → 0 ≤ Mfun δ f β cS K a →
      IsOptimalEffort δ f β cS K a (Delta δ f β K - a) := by sorry

end PlatformEntry.Protective
