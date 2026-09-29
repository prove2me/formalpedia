-- Prove2me | Theorems.Thm_TreatmentLocality_asymptotic_efficiency_of_information_sharing
-- name    : TreatmentLocality.asymptotic_efficiency_of_information_sharing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-21T16:01:38.754065+00:00
-- url     : https://prove2.me/theorems/839f4777-6941-411f-94a9-f64ee86459df
-- title:
--   Asymptotic efficiency of information sharing (Theorem 5)
-- statement:
--   **Cramér-Rao-type efficiency lower bound.** Consider an SST model $M$ with Gaussian rewards of known variance profile $v$, all transition probabilities positive, run under the mixed policy $\pi^{1/2}$ started from a stationary distribution $\nu$ of a uniformly ergodic experiment chain. Let $\delta = (\delta_T)_T$ be any sequence of measurable, square-integrable estimators of the ATE $\Delta = V^t - V^c$ from the first $T$ experiment samples that is **unbiased over the SST family**: for every SST model $M'$ with the same crucial state, discount factor and reward variance profile (Gaussian rewards with arbitrary means, arbitrary transitions), and every stationary law $\nu'$ of a uniformly ergodic experiment chain of $M'$, $E_{M',\nu'}[\delta_T] = \Delta(M')$ for all $T \ge 1$. Then for every direction $w$ and every $\varepsilon > 0$, eventually in $T$: $$w^\top \Sigma_{IS}\, w \;\le\; T\cdot \mathrm{Var}_{M,\nu}\bigl(w^\top \delta_T\bigr) + \varepsilon,$$ where $\Sigma_{IS}$ is the asymptotic covariance matrix of the model-based information-sharing estimator (`mbISCov`, the matrix of Theorem 4). In words: no unbiased estimator asymptotically beats information sharing — $\Sigma_{IS} \preceq T\Sigma$ in the limit (Theorem 5 of arXiv:2407.19618). [Formalization notes: the paper states the bound at finite $T$ via the constrained Cramér-Rao bound after an i.i.d. reduction; the formal statement takes the asymptotic (eventual, up to $\varepsilon$) form, which is what the theorem's title asserts and what survives the $O(1)$ information carried by the stationary initial state. Gaussian rewards make the reward-mean Fisher information exactly $1/\sigma^2$, matching Lemma EC.1; positivity of transitions keeps the true parameter interior to the constrained family.]
--
--   ---
--
--   **Superseded as the Theorem 5 milestone, but not retired.** This statement quantifies unbiasedness over the law of the whole experiment *trajectory*, which is strictly stronger than what arXiv:2407.19618 proves. Appendix EC.4.3 opens with "Since we assume the initial distribution is $\mu^{1/2}$, the observations $(s_i,a_i,s_{i+1},r_i)$ in $\tau$ can be seen as i.i.d.", and the Cramér-Rao computation that follows is the i.i.d. one. The formalization matching the paper is `TreatmentLocality.asymptotic_efficiency_of_information_sharing_iid`, which is now the milestone and, as of this note, is **proved in full** — its dependency tree has no open leaves.
--
--   The chain-level statement below remains a legitimate open problem. Closing it additionally requires (i) an invariant law and uniform ergodicity for each perturbed model, (ii) differentiation under the integral for the path measure, neither of which the i.i.d. reading needs. The paper's shortcut is legitimate for this particular functional because the lagged autocovariances of its influence function vanish, which is `TreatmentLocality.mbISCov_eq_integral`.
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, §4.2, Theorem 5 (Asymptotic Efficiency of Information-Sharing), with Appendix EC.4 (constrained Cramér-Rao bound, Lemmas EC.1 and EC.9)

import Definitions.Def_TreatmentLocalityEstimator
import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology

theorem TreatmentLocality.asymptotic_efficiency_of_information_sharing {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (huni : MarkovChainCLT.UniformlyErgodic (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun ω : ℕ → Step S => δ T (fun i => ω (i.1 + 1)) s) 2
      (MarkovChainCLT.chainMeasure (expKernel M) ν))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ (ν' : Measure (Step S)) (_ : IsProbabilityMeasure ν'),
        Kernel.Invariant (expKernel M') ν' →
        MarkovChainCLT.UniformlyErgodic (expKernel M') ν' →
        ∀ T : ℕ, 1 ≤ T → ∀ s,
          ∫ ω, δ T (fun i => ω (i.1 + 1)) s
            ∂(MarkovChainCLT.chainMeasure (expKernel M') ν') = M'.ate s) :
    ∀ w : S → ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
      ∑ s, ∑ s', w s * mbISCov M ν s s' * w s'
        ≤ (T : ℝ) *
          (∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s
              - ∫ ω', ∑ s, w s * δ T (fun i => ω' (i.1 + 1)) s
                  ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)) ^ 2
            ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)) + ε := by sorry
