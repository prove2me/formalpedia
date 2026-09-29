-- Prove2me | Theorems.Thm_TreatmentLocality_exists_least_favorable_score_of_unbiased
-- name    : TreatmentLocality.exists_least_favorable_score_of_unbiased
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-21T23:58:26.795107+00:00
-- url     : https://prove2.me/theorems/d4174b7d-e4e3-4e1d-804d-4eeebd5257ee
-- title:
--   Least-favourable score for the SST experiment family
-- statement:
--   **The Cramér–Rao core of the asymptotic efficiency theorem.** Consider the SST experiment of arXiv:2407.19618 run under the mixed policy $\pi^{1/2}$: Gaussian rewards with known variance profile $v$, strictly positive transitions, and a stationary law $\nu$ of a uniformly ergodic experiment chain. Let $\delta = (\delta_T)_T$ be a square-integrable estimator sequence that is unbiased for the ATE $\Delta$ across the whole SST family (same crucial state, same discount factor, same reward variances, arbitrary reward means and transitions).
--
--   Fix a direction $w \in \mathbb{R}^S$ and write $Q = w^\top \Sigma_{IS} w$ for the information-sharing asymptotic variance in that direction (`mbISCov`, the matrix of Theorem 4). The assertion is that the experiment family admits a **least-favourable score direction**: there is a constant $\kappa \ge 0$, depending on the model and on $w$ but *not* on the horizon, such that for every $T \ge 1$ there is a square-integrable function $g_T$ on the experiment path space with
--   $$\mathbb{E}[g_T] = 0, \qquad \mathbb{E}\bigl[(w^\top \delta_T)\, g_T\bigr] = Q, \qquad \mathbb{E}\bigl[g_T^2\bigr] \le (T + \kappa)\, Q.$$
--
--   Here $g_T$ is the derivative of the log-likelihood of the first $T$ experiment samples along the direction $y$ in parameter space solving the normal equations $I_{\mathrm{step}}\, y = \nabla (w^\top \Delta)$, where $I_{\mathrm{step}}$ is the per-transition Fisher information of the experiment chain. The three displayed properties are, in order: the score has mean zero; differentiating the unbiasedness identity $\mathbb{E}_{M'}[w^\top\delta_T] = w^\top\Delta(M')$ along $y$ and interchanging differentiation with integration gives $y^\top \nabla (w^\top\Delta) = y^\top I_{\mathrm{step}} y$, which the constrained Cramér–Rao computation of Appendix EC.4.3 identifies with $Q$; and the $T$-sample Fisher information is the information carried by the stationary initial state plus $T$ times the per-step information, because the per-transition scores form a martingale difference sequence — the $O(1)$ initial term being absorbed into $\kappa$.
--
--   Combined with the information inequality $\mathbb{E}[(w^\top\delta_T) g_T]^2 \le \operatorname{Var}(w^\top\delta_T)\, \mathbb{E}[g_T^2]$ this gives $Q \le (T+\kappa)\operatorname{Var}(w^\top\delta_T)$ for every $T$, and hence, letting $T \to \infty$, the asymptotic efficiency statement $w^\top\Sigma_{IS}w \le T\operatorname{Var}(w^\top\delta_T) + \varepsilon$ eventually in $T$ — Theorem 5 of arXiv:2407.19618.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.4.3 (proof of Theorem 5: the constrained Cramér–Rao bound CCRB(Δ) = ∇Δᵀ CCRB(θ) ∇Δ = Σ_IS), together with Appendix EC.8.3, Lemma EC.8 (Stoica and Ng 1998, Theorem 1) and Lemma EC.9 (Moore 2010, Corollary 3.10).

import Definitions.Def_TreatmentLocalityEstimator
import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology

theorem TreatmentLocality.exists_least_favorable_score_of_unbiased {S : Type*} [Fintype S]
    [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
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
    ∀ w : S → ℝ, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ T : ℕ, 1 ≤ T →
      ∃ g : (ℕ → Step S) → ℝ,
        MemLp g 2 (MarkovChainCLT.chainMeasure (expKernel M) ν) ∧
        ∫ ω, g ω ∂(MarkovChainCLT.chainMeasure (expKernel M) ν) = 0 ∧
        ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s) * g ω
            ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' ∧
        ∫ ω, (g ω) ^ 2 ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          ≤ ((T : ℝ) + κ) * ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by sorry
