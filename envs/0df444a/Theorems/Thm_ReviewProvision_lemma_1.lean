-- Prove2me | Theorems.Thm_ReviewProvision_lemma_1
-- name    : ReviewProvision.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:14.884207+00:00
-- url     : https://prove2.me/theorems/6b36ef14-ced7-4564-abf3-0b8e0f26a700
-- title:
--   Lemma 1, p.15 — a priori laws of $\vec v_A$ and $\vec v_G$
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales, the vector $(v_{A1},\dots,v_{AN})$ of AP evaluations has a Gaussian law and each marginal is
--
--   $$
--   v_{An}\sim N(1,\sigma^2_{An}),\qquad \sigma^2_{An}=\frac{(\tau+\eta)^2w_n}{\tau\eta[\tau\eta+(\tau+\eta)w_n]}.
--   $$
--
--   The vector $(v_{G1},\dots,v_{GN})$ of GP evaluations has a Gaussian law, and if $S_1>0$ each marginal is
--
--   $$
--   v_{Gn}\sim N(1,\sigma^2_{Gn}),\qquad \sigma^2_{Gn}=\frac{(\tau w_n+\eta S_1)^2}{\tau\eta(\tau\eta S_1+\tau S_2+\eta S_1^2)}.
--   $$
--
--   More information means more variance in the evaluation: this lemma turns the comparison of policies into a comparison of these variances.
--
--   **Formalization Note** A Gaussian law here allows a degenerate covariance, and $N(1,0)$ is the point mass at $1$.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - reading: v_{An}|(θk_n, r_n) ∼ N(q_p, σ²_{An}), and likewise for GP → the unconditional law of v_{An} is N(1, σ²_{An}); reason: given r_n the value v_{An} is a constant; p.15 calls these the 'a priori' distributions
--   - encoding: the GP marginal for all sales → the hypothesis S_1 > 0 on the GP marginal; reason: σ²_{Gn} is 0/0 at S_1 = 0; the vector law is still stated there
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Lemma 1, p.15

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Lemma 1**, SSRN 3403322 (manuscript of 2021-05-24), p.15 (PDF 15): under AP and GP the vector
of customer evaluations is multivariate Normal, with marginals `v_{An} ∼ N(1, σ²_{An})` and
`v_{Gn} ∼ N(1, σ²_{Gn})`.

**Formalization Note.** The laws are the unconditional, "a priori" ones (p.15): the paper's
`v_{An}|(θ k_n, r_n)` is a constant. `HasGaussianLaw` allows a degenerate covariance. The GP marginal is
guarded by `0 < S_1` because `σ²_{Gn}` is `0/0` otherwise. -/
theorem lemma_1 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) :
    HasGaussianLaw (fun ω n => posteriorMean p k .AP n ω) (prior p N) ∧
    (∀ n, HasLaw (posteriorMean p k .AP n)
      (gaussianReal 1 (sigmaSqA p (weight p k) n).toNNReal) (prior p N)) ∧
    HasGaussianLaw (fun ω n => posteriorMean p k .GP n ω) (prior p N) ∧
    (0 < S1 (weight p k) → ∀ n, HasLaw (posteriorMean p k .GP n)
      (gaussianReal 1 (sigmaSqG p (weight p k) n).toNNReal) (prior p N)) := by sorry

end ReviewProvision
