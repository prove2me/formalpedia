-- Prove2me | Theorems.Thm_ReviewProvision_eq_13
-- name    : ReviewProvision.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:52.034996+00:00
-- url     : https://prove2.me/theorems/1942c5e9-aeb2-4afb-8c9b-94f9fc36235e
-- title:
--   Eq. (13), p.24 — a priori law under JP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales, the vector $(v_{J1},\dots,v_{JN})$ of JP evaluations has a Gaussian law, and for a cluster $n$ with $S_1'>0$ the marginal is $v_{Jn}\sim N(1,\sigma^2_{Jn})$ with
--
--   $$
--   \sigma^2_{Jn}=\frac{\eta^3S_1'^2+(\tau+\eta)w_n[\eta S_1'(\tau+\eta+S_1')+(\tau+\eta)S_2']}{\tau\eta\{[\tau(\eta+w_n)+\eta w_n](\eta S_1'+S_2')+\eta(\eta+w_n)S_1'^2\}}.
--   $$
--
--   This is the variance that drives the firm's profit under JP.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: (13) for all sales → the hypothesis S′_1 > 0 on the marginal; reason: (13) is 0/0 at S′_1 = 0; the vector law is still stated there
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (13), p.24; Appendix A, part III, pp.35–36

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (13)**, SSRN 3403322 (manuscript of 2021-05-24), p.24 (PDF 24), with Appendix A, part III,
pp.35–36 (PDF 35–36): the vector `(v_{J1}, …, v_{JN})` is multivariate Normal and, when `S′_1 > 0`,
`v_{Jn} ∼ N(1, σ²_{Jn})`.

**Formalization Note.** The marginal is guarded by `0 < S′_1` because (13) is `0/0` otherwise. -/
theorem eq_13 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) :
    HasGaussianLaw (fun ω n => posteriorMean p k .JP n ω) (prior p N) ∧
    ∀ n, 0 < S1' (weight p k) n → HasLaw (posteriorMean p k .JP n)
      (gaussianReal 1 (sigmaSqJ p (weight p k) n).toNNReal) (prior p N) := by sorry

end ReviewProvision
