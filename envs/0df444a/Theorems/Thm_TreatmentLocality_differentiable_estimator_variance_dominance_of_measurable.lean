-- Prove2me | Theorems.Thm_TreatmentLocality_differentiable_estimator_variance_dominance_of_measurable
-- name    : TreatmentLocality.differentiable_estimator_variance_dominance_of_measurable
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-21T17:45:08.588414+00:00
-- url     : https://prove2.me/theorems/a279be78-ddd5-49e7-88ce-4a81668a02e4
-- title:
--   Variance reduction for differentiable estimators (Theorem 9), measurable estimator
-- statement:
--   **Theorem 9 of arXiv:2407.19618, with the estimator required to be measurable.**
--
--   Consider an SST model $M$ run under the mixed policy $\pi^{1/2}$, with the experiment-tuple chain uniformly ergodic with stationary law $\nu$ and square-integrable rewards. Let $\hat\Delta_\Gamma=f(K^t_\Gamma,K^c_\Gamma,R^t_\Gamma,R^c_\Gamma)$ for $\Gamma\in\{AB,IS\}$ be a differentiable estimator: $f$ is Fréchet-differentiable at the mean statistics. Then:
--
--   1. **Same asymptotic bias** — the mean statistics of the two schemes coincide, so both estimators are centred at the same limit value $f(\ell)$.
--   2. **Asymptotic normality** — for each scheme, $\sqrt T(\hat\Delta_\Gamma-f(\ell))\xrightarrow{d}N(0,\sigma_\Gamma^2)$ with $\sigma_\Gamma^2=\nabla f^\top\Sigma_\Gamma\nabla f$ the asymptotic variance of the linearized observable.
--   3. **Decomposition and dominance** — writing $\Sigma_\Gamma=\Sigma^{inst}_\Gamma+\Sigma^{cov}_\Gamma$: the temporal parts agree, $\Sigma^{cov}_{IS}=\Sigma^{cov}_{AB}$; the instantaneous parts agree on every row and column attached to the crucial state $s^1$, so the variance *at the treated state cannot be reduced*; the difference $\Sigma^{inst}_{AB}-\Sigma^{inst}_{IS}$ is positive semidefinite; and consequently $\Sigma_{IS}\preceq\Sigma_{AB}$ in the Loewner order.
--
--   Information sharing never increases the asymptotic variance of any differentiable estimator, and the entire reduction happens away from the treated state.
--
--   **Why measurability appears.** The asymptotic-normality clause asserts convergence in distribution, which in Mathlib carries an almost-everywhere measurability obligation on each $\omega\mapsto f(\text{empirical statistics}(\omega))$. Fréchet-differentiability at the single point $\ell$ does not supply it: $f(v)=\|v-\ell\|^2\mathbf 1_A(v)$ with $A$ non-measurable is differentiable at $\ell$ with derivative $0$ and measurable nowhere else, and the empirical statistics have a non-atomic law as soon as the rewards do. The paper's Definition 1 treats $f$ as differentiable, and Appendix EC.3.2 uses "$f$ is differentiable (and thus continuous)", so the hypothesis is present in the source and costs nothing; it is stated explicitly here because the formal conclusion needs it.
--
--   The measurability hypothesis is used only for the asymptotic-normality clause. The other four clauses are pure identities about the covariance structure of the two schemes and hold for an arbitrary $f$.
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, Section 6.2, Theorem 9, with the decomposition computed in Appendix EC.3.2. Differs from TreatmentLocality.differentiable_estimator_variance_dominance only by the added hypothesis that the estimator f is measurable, which the convergence-in-distribution conclusion requires and which differentiability at a single point does not supply; Definition 1 and Appendix EC.3.2 both treat f as differentiable, hence continuous, hence measurable.

import Definitions.Def_TreatmentLocalityEstimator
import Definitions.Def_MarkovErgodicity
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology

theorem TreatmentLocality.differentiable_estimator_variance_dominance_of_measurable
    {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (huni : MarkovChainCLT.UniformlyErgodic (expKernel M) ν)
    (hL2 : M.RewardL2)
    (f : EstInput S → ℝ) (hfm : Measurable f) (f' : EstInput S →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' (meanObs M .AB ν)) :
    meanObs M .AB ν = meanObs M .IS ν
    ∧ (∀ Γ : Scheme, TendstoInDistribution
        (fun (T : ℕ) (ω : ℕ → Step S) =>
          Real.sqrt T * (f (empAvg M Γ T ω) - f (meanObs M .AB ν)))
        atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure (expKernel M) ν)
        (gaussianReal 0
          (MarkovChainCLT.asymptoticVariance (expKernel M) ν
            (fun z => f' (estObs M Γ z))).toNNReal))
    ∧ lagCovMatrix M .AB ν = lagCovMatrix M .IS ν
    ∧ (∀ p q : EstIdx S, idxState p = M.crucial ∨ idxState q = M.crucial →
        instCovMatrix M .AB ν p q = instCovMatrix M .IS ν p q)
    ∧ Matrix.PosSemidef (instCovMatrix M .AB ν - instCovMatrix M .IS ν)
    ∧ Matrix.PosSemidef (asymCovMatrix M .AB ν - asymCovMatrix M .IS ν) := by sorry
