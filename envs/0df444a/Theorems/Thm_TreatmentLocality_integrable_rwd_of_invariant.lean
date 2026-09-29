-- Prove2me | Theorems.Thm_TreatmentLocality_integrable_rwd_of_invariant
-- name    : TreatmentLocality.integrable_rwd_of_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:14:46.539821+00:00
-- url     : https://prove2.me/theorems/478f1d8e-5528-450a-8a49-0308b743e943
-- title:
--   Integrability of the reward under an invariant experiment law
-- statement:
--   **Integrability of the reward along a stationary experiment.** Consider the SST experiment of arXiv:2407.19618 run under the mixed policy $\pi^{1/2}$, whose trajectory $X_i = (s_i, \gamma_i, s_{i+1}, r_i)$ is a Markov chain on the space of one step. If each of the finitely many reward laws $\mathrm{reward}(s,a)$ has a first moment, then under any invariant law $\nu$ of the experiment chain the realized reward is integrable:
--   $$\mathbb{E}_\nu\bigl[\,|r|\,\bigr] < \infty .$$
--
--   The point is that no assumption on $\nu$ beyond invariance is needed. Invariance rewrites the expectation as an average of one-step expectations, and the one-step law at any state is a fair mixture of two of the finitely many reward laws; so the moment is bounded, uniformly in the state, by the total moment over all state-action pairs. This is the hypothesis under which the linearisation of a model-based estimator — which is linear in the reward — is integrable.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2-§3 (the SST model, the mixed policy π^{1/2} and the experiment trajectory) and Appendix EC.3.1 (the stationary law of the experiment chain and its moment assumptions).

import Definitions.Def_TreatmentLocality
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.integrable_rwd_of_invariant {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) :
    Integrable (fun z : Step S => Step.rwd z) ν := by sorry
