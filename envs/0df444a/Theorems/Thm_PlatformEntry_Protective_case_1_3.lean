-- Prove2me | Theorems.Thm_PlatformEntry_Protective_case_1_3
-- name    : PlatformEntry.Protective.case_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:41.082665+00:00
-- url     : https://prove2.me/theorems/6b739eaa-2110-444c-bddc-802c440a369c
-- title:
--   Case 1.3 of the proof of Proposition 3, PDF p. 36 — for large a the effort e^B_E(a) is optimal
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy (5) and $H\le 1/4$, let $c_S>1/2$, $K>0$, and let $\underline a_1+e^B_N(\underline a_1)=\Delta$. Then for every base value $a\ge\underline a_1$ with
--   $$\Pi^S_N(\Delta-a)\le\Pi^S_E\big(e^B_E(a)\big)\quad\text{and}\quad a+e^B_E(a)>\Delta,$$
--   the entry first-best $e^B_E(a)$ maximizes the seller's total profit $\Pi^S$ over all $e_S\in\mathbb R$.
--
--   For high base values deterring entry would need too large a distortion, so the seller accepts entry and invests at the entry first-best.
--
--   **Formalization Note** In the paper the case is $a\ge\bar a_1$; the proof uses it through the two displayed inequalities and through $a\ge\bar a_1\ge\underline a_1$. Those three facts are the hypotheses, so the milestone does not depend on the definition of $\bar a_1$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, Case 1.3, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Case 1.3 of the proof of Proposition 3, PDF p. 36: for a ≥ a₁ with
Π^S_N(Δ − a) ≤ Π^S_E(e^B_E(a)) and a + e^B_E(a) > Δ (what a ≥ ā₁ provides),
the first-best effort e^B_E(a) is optimal. -/
theorem case_1_3 (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS) (hK : 0 < K)
    (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) (a₁ : ℝ)
    (ha₁ : a₁ + eBN f cS a₁ = Delta δ f β K) :
    ∀ a : ℝ, a₁ ≤ a → Mfun δ f β cS K a ≤ 0 → Delta δ f β K < a + eBE δ f β cS a →
      IsOptimalEffort δ f β cS K a (eBE δ f β cS a) := by sorry

end PlatformEntry.Protective
