-- Prove2me | Theorems.Thm_ReviewProvision_eq_12
-- name    : ReviewProvision.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:07.573623+00:00
-- url     : https://prove2.me/theorems/3ef35851-6459-42ec-ad3b-23dd0c781cce
-- title:
--   Eq. (12), p.23 — a priori law under FP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales, the vector $(v_{F1},\dots,v_{FN})$ of FP evaluations has a Gaussian law, and each marginal is $v_{Fn}\sim N(1,\sigma^2_{Fn})$ with
--
--   $$
--   \sigma^2_{Fn}=\frac{w_n(\tau+T)[\tau(\eta+w_n)+\eta w_n]+2\eta^2w_n(\tau+T)+\eta^3T}{\tau\eta(\eta+w_n)^2(\tau+T)},\qquad T=\sum_l\frac{\eta w_l}{\eta+w_l}.
--   $$
--
--   This is the variance that drives the firm's profit under FP.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - reading: T := Σ_{l=1}^N ηw_n/(η+w_n), with the summand printed with index n → T = Σ_l ηw_l/(η+w_l); reason: the sum runs over l, so the index n of the printed summand is a misprint; p.35 prints the same T with index l
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (12), p.23; Appendix A, part III, p.35

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (12)**, SSRN 3403322 (manuscript of 2021-05-24), p.23 (PDF 23), with Appendix A, part III,
p.35 (PDF 35): the vector `(v_{F1}, …, v_{FN})` is multivariate Normal and `v_{Fn} ∼ N(1, σ²_{Fn})`. -/
theorem eq_12 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) :
    HasGaussianLaw (fun ω n => posteriorMean p k .FP n ω) (prior p N) ∧
    ∀ n, HasLaw (posteriorMean p k .FP n)
      (gaussianReal 1 (sigmaSqF p (weight p k) n).toNNReal) (prior p N) := by sorry

end ReviewProvision
