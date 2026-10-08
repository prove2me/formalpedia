-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_distribution_dependent_lower_bound
-- name    : RegretBandits.Stochastic.distribution_dependent_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:10.492661+00:00
-- url     : https://prove2.me/theorems/6340c688-9508-46ab-9268-eda97a9bae48
-- title:
--   Theorem 2.2 — distribution-dependent lower bound
-- statement:
--   Let $\pi$ be a strategy for $K\ge2$ arms (possibly randomized, not depending on the horizon). Assume that $\pi$ is consistent: for every Bernoulli bandit with means $\mu'\in[0,1]^K$, every arm $i$ with $\Delta_i>0$ and every $a>0$,
--   $$\mathbb E\,T_i(n)=o(n^a)\qquad(n\to\infty).$$
--   Then for every Bernoulli bandit with means $\mu\in[0,1]^K$,
--   $$\liminf_{n\to+\infty}\frac{\overline R_n}{\ln n}\ge\sum_{i:\Delta_i>0}\frac{\Delta_i}{\mathrm{kl}(\mu_i,\mu^*)}.$$
--
--   The theorem shows that the $\ln n$ growth of Theorem 2.1 is optimal for consistent strategies, and identifies the optimal constant for Bernoulli rewards.
--
--   **Formalization Note.** If $\mu^*=1$ then $\mathrm{kl}(\mu_i,1)=+\infty$ and the term is $0$; this case is written out. The $\liminf$ is taken in the extended reals. The consistency hypothesis is stated for every probability space carrying a Bernoulli bandit and the strategy's seeds; since the law of the run does not depend on the space, this is the book's hypothesis. The book proves the theorem for $K=2$ only ("For simplicity"); the statement is for every $K\ge2$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 13, Theorem 2.2

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_klBernoulli
import Definitions.Def_RegretBandits_Stochastic_strategy

namespace RegretBandits.Stochastic

open MeasureTheory Filter Topology ImprovedLinBandits.UCBDelta

/-- Theorem 2.2 of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 13): let `π` be a strategy such
that `𝔼 T_i(n) = o(n^a)` for every Bernoulli bandit, every arm `i` with `Δ_i > 0` and every
`a > 0`. Then for every Bernoulli bandit
`liminf_{n → ∞} R̄_n / ln n ≥ ∑_{i : Δ_i > 0} Δ_i / kl(μ_i, μ*)`,
where a term with `μ* = 1` (so `kl(μ_i, 1) = +∞`) is `0`. -/
theorem distribution_dependent_lower_bound {K : ℕ} (hK : 2 ≤ K) (π : Strategy K)
    (hcons : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (μ' : Fin K → ℝ) (X' : Fin K → ℕ → Ω' → ℝ) (U' : ℕ → Ω' → ℝ),
      IsBernoulliModel P' μ' X' U' → ∀ i, 0 < gap μ' i → ∀ a : ℝ, 0 < a →
        Tendsto (fun n : ℕ =>
            (∫ ω, (pullCount (strategyArm π X' U') i n ω : ℝ) ∂P') / (n : ℝ) ^ a)
          atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Fin K → ℝ) (X : Fin K → ℕ → Ω → ℝ) (U : ℕ → Ω → ℝ) (hB : IsBernoulliModel P μ X U) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        ((if bestMean μ < 1 then gap μ i / klBern (μ i) (bestMean μ) else 0 : ℝ) : EReal)) ≤
      liminf (fun n : ℕ =>
        ((pseudoRegretBar P μ (strategyArm π X U) n / Real.log (n : ℝ) : ℝ) : EReal)) atTop := by sorry

end RegretBandits.Stochastic
