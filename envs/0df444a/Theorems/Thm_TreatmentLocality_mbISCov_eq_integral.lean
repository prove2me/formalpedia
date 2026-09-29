-- Prove2me | Theorems.Thm_TreatmentLocality_mbISCov_eq_integral
-- name    : TreatmentLocality.mbISCov_eq_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:41.450211+00:00
-- url     : https://prove2.me/theorems/08aae31b-7ab0-4a00-acd9-766af12478a7
-- title:
--   The asymptotic covariance $\Sigma_{IS}$ is instantaneous
-- statement:
--   **The asymptotic covariance of the model-based information-sharing estimator is instantaneous.** In general the asymptotic covariance of a statistic along a stationary Markov chain is $\Sigma = \mathrm{Var}[\varphi(X_1)] + \sum_{k\ge 1}\mathrm{Cov}[\varphi(X_1), \varphi(X_{1+k})] + \sum_{k\ge 1}\mathrm{Cov}[\varphi(X_{1+k}), \varphi(X_1)]$. For the linearisation $\varphi$ of the model-based information-sharing estimator, under an invariant law $\nu$ with all states visited and integrable rewards, every lagged term vanishes and
--   $$\Sigma_{\mathrm{IS}}(s,s') \;=\; \mathbb{E}_\nu\bigl[\varphi_s\,\varphi_{s'}\bigr].$$
--
--   The reason is that $\varphi$ is a martingale difference along the experiment chain: its conditional mean given the past is zero at every step, so its $k$-step conditional expectation is zero for every $k \ge 1$ and its unconditional mean is zero as well. Both series therefore consist entirely of zeros, and the lag-$0$ term reduces to the plain second moment.
--
--   This identifies $\Sigma_{\mathrm{IS}}$ with the second moment of a single weighted temporal-difference error — the form in which it is matched against the constrained Cramér-Rao bound in the efficiency theorem (arXiv:2407.19618, Theorems 3-5 and Appendix EC.3.2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Remark 1 and Proposition 5 (the model-based plug-in estimator), §6.2 (the information-sharing statistics), and Appendix EC.3.2 (the linearisation of a differentiable estimator and its asymptotic covariance, Lemma EC.4-EC.5).

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.mbISCov_eq_integral {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) :
    mbISCov M ν s s'
      = ∫ z, (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                (estObs M .IS z))
            * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
                (estObs M .IS z)) ∂ν := by sorry
