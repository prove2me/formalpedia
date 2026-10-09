-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_4
-- name    : PrimalDualPricing.Regret.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:26:49.809069+00:00
-- url     : https://prove2.me/theorems/e7e982d2-7c30-4f36-8f67-4c5dcec631aa
-- title:
--   Lemma 4, p. 14 — $\mathbb P(C_{k+1}\mid B_k\cap C_k\cap B_{k+1})=1-O(1/n)$
-- statement:
--   Under Assumptions 1–2 and Remark 2, with the events $B_k$, $C_k$ of the interval estimators of Algorithm 1, for every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$ and $k$, such that for every $n\ge3$ and every $k=1,\dots,K-1$,
--   $$\mathbb P\big(C_{k+1}^{c}\cap B_k\cap C_k\cap B_{k+1}\big)\le\frac Cn\,\mathbb P\big(B_k\cap C_k\cap B_{k+1}\big),$$
--   i.e. $\mathbb P(C_{k+1}\mid B_k\cap C_k\cap B_{k+1})=1-O(1/n)$.
--
--   **Formalization Note** The product form and the readings of $O(\cdot)$ and "sufficiently small $\epsilon$" are as in Lemma 3. The page prints no range for $k$; the range $k=1,\dots,K-1$ of Lemma 3 is used, the one for which $C_{k+1}$ is defined.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 14, Lemma 4

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 4 (Chen–Gallego, arXiv:1812.09234v3, p. 14), in product form:
`P(C_{k+1} | B_k ∩ C_k ∩ B_{k+1}) = 1 − O(1/n)`, for `k = 1, …, K − 1`. Under Assumptions 1–2 and Remark 2,
for every sufficiently small `ε > 0` there is `C`, independent of `n` and `k`, such that for every `n ≥ 3`
and `1 ≤ k ≤ K − 1`, `P(C_{k+1}ᶜ ∩ B_k ∩ C_k ∩ B_{k+1}) ≤ (C/n) P(B_k ∩ C_k ∩ B_{k+1})`. -/
theorem lemma_4 {M : ℕ} (S : Setting M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, 1 ≤ k → k + 1 ≤ numPhases eps n →
          (ℙ ((S.eventC eps n N (k + 1))ᶜ ∩ S.eventB eps n N k ∩ S.eventC eps n N k
              ∩ S.eventB eps n N (k + 1))).toReal
            ≤ C / n * (ℙ (S.eventB eps n N k ∩ S.eventC eps n N k
              ∩ S.eventB eps n N (k + 1))).toReal := by sorry

end PrimalDualPricing.Regret
