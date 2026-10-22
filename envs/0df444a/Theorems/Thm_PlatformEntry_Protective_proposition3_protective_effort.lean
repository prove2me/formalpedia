-- Prove2me | Theorems.Thm_PlatformEntry_Protective_proposition3_protective_effort
-- name    : PlatformEntry.Protective.proposition3_protective_effort
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:36.260484+00:00
-- url     : https://prove2.me/theorems/04d8822d-1db9-4f22-8978-0940c704f56d
-- title:
--   Proposition 3, PDF p. 18 — in the protective regime the seller underinvests to deter entry exactly for intermediate base values
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5) and lie in the protective regime $\overline\Omega=\{H\le 1/4\}$, and let $c_S>1/2$ and $K>0$. Let $\Delta$ be the platform's entry threshold, $e^B_N,e^B_E$ the benchmark efforts (9)–(10), and $\Pi^S$ the seller's total profit, equal to $\Pi^S_N(e_S)$ if $e_S+a\le\Delta$ and to $\Pi^S_E(e_S)$ otherwise. Then:
--
--   1. With $\underline a_1$ defined by $\underline a_1+e^B_N(\underline a_1)=\Delta$, there is $\bar a_1\ge\underline a_1$ such that for every base value $a\in\mathbb R$ an optimal effort $e^*_S(a)$ (a maximizer of $\Pi^S$ over $\mathbb R$) is
--   $$e^*_S(a)=\begin{cases}e^B_N(a)& a\le\underline a_1,\\ \Delta-a & a\in(\underline a_1,\bar a_1),\\ e^B_E(a)& a\ge\bar a_1.\end{cases}$$
--   2. For every base value $a$ and effort $e_S$, the stage-1 quantity $q_1^*=(a+e_S)/2$ maximizes the seller's stage-1 profit $q_1(a+e_S-q_1)(1-f)-c_Se_S^2$; in particular $q^*_1=(a+e^*_S(a))/2$.
--
--   When the platform would be unwelcome, the seller follows her first-best for small and for large base values but deliberately underinvests for intermediate ones, holding the product's value at the entry threshold to keep the platform out.
--
--   **Formalization Note** "Optimal" means a global maximizer with ties allowed; at $a=\bar a_1$ both $\Delta-a$ and $e^B_E(a)$ are optimal, and when $H=1/4$ the middle interval is empty. Efforts range over all reals; the optimal effort $\Delta-a$ can be negative, and with $e_S\ge0$ the statement would be false. Condition (5) (a standing assumption of the paper) and $K>0$ (presupposed by the formula for $\Delta$) are hypotheses; the paper's proof also covers the case where (5) fails, which is not formalized. The quantity claim holds for every effort, so it is stated for all $e_S$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF p. 18, Proposition 3; proof in Online Supplement, Appendix A, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Proposition 3, PDF p. 18: in the protective regime PlatformEntry.Regimes.H ≤ 1/4, with a₁ defined by
a₁ + e^B_N(a₁) = Δ, there is ā₁ ≥ a₁ such that the optimal effort is e^B_N(a) for a ≤ a₁,
Δ − a for a ∈ (a₁, ā₁), and e^B_E(a) for a ≥ ā₁; the optimal stage-1 quantity is (a + e_S)/2. -/
theorem proposition3_protective_effort (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS)
    (hK : 0 < K) (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) :
    (∃ a₁ ā₁ : ℝ, a₁ + eBN f cS a₁ = Delta δ f β K ∧ a₁ ≤ ā₁ ∧
      ∀ a : ℝ,
        (a ≤ a₁ → IsOptimalEffort δ f β cS K a (eBN f cS a)) ∧
        (a₁ < a → a < ā₁ → IsOptimalEffort δ f β cS K a (Delta δ f β K - a)) ∧
        (ā₁ ≤ a → IsOptimalEffort δ f β cS K a (eBE δ f β cS a))) ∧
    (∀ a e q : ℝ, PlatformEntry.Regimes.stage1Seller f cS a e q ≤ PlatformEntry.Regimes.stage1Seller f cS a e ((a + e) / 2)) := by sorry

end PlatformEntry.Protective
