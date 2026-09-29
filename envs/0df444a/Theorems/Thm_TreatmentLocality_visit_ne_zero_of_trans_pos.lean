-- Prove2me | Theorems.Thm_TreatmentLocality_visit_ne_zero_of_trans_pos
-- name    : TreatmentLocality.visit_ne_zero_of_trans_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:14:56.710437+00:00
-- url     : https://prove2.me/theorems/e9160d27-58cc-42df-b788-af32fecc1e67
-- title:
--   Positive stationary visit probability of every state
-- statement:
--   **Every state is visited with positive stationary probability.** Consider the SST experiment of arXiv:2407.19618 under the mixed policy $\pi^{1/2}$, and suppose all transition probabilities are strictly positive: $P(j \mid s, a) > 0$ for every state $s$, arm $a$ and target $j$. Then for any invariant law $\nu$ of the experiment chain and every state $i$,
--   $$\mu(i) \;=\; \mathbb{P}_\nu[s = i] \;>\; 0 .$$
--
--   Two steps: under an invariant law the current state and the next state have the same distribution, and the next state equals $i$ with conditional probability at least $\tfrac12 P(i \mid s, t)$ whatever the current state $s$ is — a quantity bounded below by a positive constant because the state space is finite. Positivity of the visit probabilities is exactly what makes the plug-in normalisation $K^a(i,j)/\sum_k K^a(i,k)$ legitimate at the population point, and hence the model-based estimator differentiable there.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2-§3 (the SST model, the mixed policy π^{1/2} and the experiment trajectory) and Appendix EC.3.1 (the stationary law of the experiment chain and its moment assumptions).

import Definitions.Def_TreatmentLocality
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.visit_ne_zero_of_trans_pos {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) (i : S) :
    ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0 := by sorry
