-- Prove2me | Theorems.Thm_QLearning_Convergence_stochastic_averaging_converges_ae
-- name    : QLearning.Convergence.stochastic_averaging_converges_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:14.519136+00:00
-- url     : https://prove2.me/theorems/e1f47a8a-9b39-455f-8b9b-3a69d033d688
-- title:
--   Proof of Lemma B.3, p. 290 — X_{n+1} = X_n + β_n(ξ_n − X_n) with Σβ = ∞, Σβ² < ∞ and bounded ξ_n of mean Ξ converges to Ξ a.s.
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space with a filtration $(\mathcal F_n)_{n\ge0}$. Let $X_n$ be real random variables updated according to
--   $$X_{n+1}=X_n+\beta_n(\xi_n-X_n),$$
--   where $X_0$ is $\mathcal F_0$-measurable; the step $\beta_n$ is $\mathcal F_n$-measurable with $0\le\beta_n<1$; the noise $\xi_n$ is $\mathcal F_{n+1}$-measurable, bounded by a constant $C$, and has conditional mean $\mathbb E[\xi_n\mid\mathcal F_n]=\Xi$; and almost surely $\sum_n\beta_n=\infty$ and $\sum_n\beta_n^2<\infty$. Then
--   $$X_n\to\Xi\quad\text{as }n\to\infty,\ \text{with probability }1.$$
--
--   This is the standard stochastic-convergence theorem (Kushner and Clark 1978, Theorem 2.3.1) that the paper quotes in the proof of Lemma B.3, where it is applied to the ARP's rewards and transition probabilities with $\beta$ the learning rates at the visits of a state–action pair.
--
--   **Formalization Note** The page says only that the $\xi_n$ are "bounded random variables with mean $\Xi$". The statement pins the martingale-difference reading $\mathbb E[\xi_n\mid\mathcal F_n]=\Xi$ with adapted random steps, because in Lemma B.3 the steps are learning rates at random visit times; the reading with deterministic steps and independent $\xi_n$ is a special case. Indices start at $n=0$.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 290, proof of Lemma B.3, first two displays (quoting Kushner & Clark 1978, Theorem 2.3.1)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem stochastic_averaging_converges_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Xs β ξ : ℕ → Ω → ℝ) (Ξ C : ℝ)
    (hrec : ∀ n ω, Xs (n + 1) ω = Xs n ω + β n ω * (ξ n ω - Xs n ω))
    (hX0 : StronglyMeasurable[ℱ 0] (Xs 0))
    (hβm : ∀ n, StronglyMeasurable[ℱ n] (β n))
    (hβ : ∀ n ω, 0 ≤ β n ω ∧ β n ω < 1)
    (hξm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ n))
    (hξb : ∀ n ω, |ξ n ω| ≤ C)
    (hξmean : ∀ n, μ[ξ n | ℱ n] =ᵐ[μ] fun _ => Ξ)
    (hsteps : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, β n ω) atTop atTop ∧
      Summable (fun n => β n ω ^ 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Xs n ω) atTop (𝓝 Ξ) := by sorry

end QLearning.Convergence
