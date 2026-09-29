-- Prove2me | Theorems.Thm_TreatmentLocality_integrable_rwd_iterKernel
-- name    : TreatmentLocality.integrable_rwd_iterKernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:14:51.748285+00:00
-- url     : https://prove2.me/theorems/6aa926ee-01ed-4a5b-9d60-0f7e98ab33f9
-- title:
--   Integrability of the reward at every step of the experiment chain
-- statement:
--   **Integrability of the reward at every step of the chain.** For the SST experiment of arXiv:2407.19618, if each of the finitely many reward laws has a first moment then the realized reward is integrable under the $k$-step transition kernel started from *any* step $x$, for every $k$:
--   $$\int |r|\; \mathrm{d}P^{k}(x, \cdot) < \infty .$$
--
--   For $k = 0$ the kernel is a point mass and the statement is trivial; for $k \ge 1$ the last step is drawn from the one-step experiment law at some state, whose reward moment is bounded uniformly in the state by the total moment over the finitely many state-action pairs. The uniformity in both $k$ and the starting point is what makes the lagged autocovariances of an unbounded functional well defined.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2-§3 (the SST model, the mixed policy π^{1/2} and the experiment trajectory) and Appendix EC.3.1 (the stationary law of the experiment chain and its moment assumptions).

import Definitions.Def_TreatmentLocality
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.integrable_rwd_iterKernel {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) (k : ℕ) (x : Step S) :
    Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x) := by sorry
