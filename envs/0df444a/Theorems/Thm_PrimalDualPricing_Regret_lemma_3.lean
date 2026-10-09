-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_3
-- name    : PrimalDualPricing.Regret.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:25:40.425872+00:00
-- url     : https://prove2.me/theorems/958a8e05-2410-4a2d-ab51-16a8beb9066a
-- title:
--   Lemma 3, p. 14 — $\mathbb P(B_{k+1}\mid B_k\cap C_k)=1-O(1/n)$ for $k=1,\dots,K-1$
-- statement:
--   Under Assumptions 1–2 and Remark 2, consider Algorithm 1 run on independent unit-rate Poisson arrivals. Let $B_k$ be the event that $z^*$ lies in the dual interval estimator of phase $k$, and $C_k$ the event that $\mathcal P_m(z)$ lies in the price interval estimator of phase $k$ for every $m$ and every $z$ in the dual interval estimator. Then for every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$ and $k$, such that for every $n\ge3$ and every $k=1,\dots,K-1$,
--   $$\mathbb P\big(B_{k+1}^{c}\cap B_k\cap C_k\big)\le\frac Cn\,\mathbb P\big(B_k\cap C_k\big),$$
--   i.e. $\mathbb P(B_{k+1}\mid B_k\cap C_k)=1-O(1/n)$.
--
--   **Formalization Note** The conditional probability is stated in product form, which remains meaningful when $B_k\cap C_k$ has probability $0$. $O(1/n)$ is read as "at most $C/n$ for all $n\ge3$, with $C$ independent of $n$ and $k$". "Sufficiently small $\epsilon$" (p. 13) is read as "every $\epsilon\in(0,\epsilon_0)$ for some $\epsilon_0>0$". The constant may depend on the model and on $\epsilon$. It does not depend on the probability space.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 14, Lemma 3 (events p. 14)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 3 (Chen–Gallego, arXiv:1812.09234v3, p. 14), in product form:
`P(B_{k+1} | B_k ∩ C_k) = 1 − O(1/n)` for `k = 1, …, K − 1`. Under Assumptions 1–2 and Remark 2
(`Setting`), for every sufficiently small `ε > 0` there is `C`, independent of `n` and `k`, such that for
`M` independent unit-rate Poisson paths on any probability space, every `n ≥ 3` and every
`1 ≤ k ≤ K − 1`, `P(B_{k+1}ᶜ ∩ B_k ∩ C_k) ≤ (C/n) P(B_k ∩ C_k)` for Algorithm 1 with parameter `ε`. -/
theorem lemma_3 {M : ℕ} (S : Setting M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, 1 ≤ k → k + 1 ≤ numPhases eps n →
          (ℙ ((S.eventB eps n N (k + 1))ᶜ ∩ S.eventB eps n N k ∩ S.eventC eps n N k)).toReal
            ≤ C / n * (ℙ (S.eventB eps n N k ∩ S.eventC eps n N k)).toReal := by sorry

end PrimalDualPricing.Regret
