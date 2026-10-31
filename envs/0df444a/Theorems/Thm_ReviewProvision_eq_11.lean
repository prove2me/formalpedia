-- Prove2me | Theorems.Thm_ReviewProvision_eq_11
-- name    : ReviewProvision.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:19.449987+00:00
-- url     : https://prove2.me/theorems/7434d28a-36b3-4ee6-8d8a-0a9d31736d47
-- title:
--   Eq. (11), p.23 — posterior mean under FP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales, with $T=\sum_l\eta w_l/(\eta+w_l)$ and every cluster $n$, the customer evaluation under FP satisfies, almost surely,
--
--   $$
--   v_{Fn}=\frac{\tau\eta+(\tau+T)\,y_n+\eta\sum_{i=1}^N\frac{\eta\,y_i}{\eta+w_i}}{(\eta+w_n)(\tau+T)}.
--   $$
--
--   This is the Bayes update of the cluster value given all $N$ ratings.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: (11) with q_p and w_i r_i → the statistic y_n = w_n(q + t_n) + √w_n ε_n, with q_p = 1; reason: y_n = w_n r_n generates the same information when w_n > 0 and is 0 when no ratings exist; q_p = 1 as in §3.1
--   - reading: T := Σ_{l=1}^N ηw_n/(η+w_n), with the summand printed with index n → T = Σ_l ηw_l/(η+w_l); reason: the sum runs over l, so the index n of the printed summand is a misprint; p.35 prints the same T with index l
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (11), p.23

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (11)**, SSRN 3403322 (manuscript of 2021-05-24), p.23 (PDF 23): the FP posterior mean, with
`q_p = 1`, `T = Σ_l ηw_l/(η+w_l)` and `w_i r_i = y_i`:
`v_{Fn} = (τη + (τ+T) y_n + η Σ_i η y_i/(η+w_i)) / ((η+w_n)(τ+T))` almost surely.

**Formalization Note.** Written with the statistic `y`, the formula holds for every feasible `~k`. -/
theorem eq_11 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) (n : Fin N) :
    posteriorMean p k .FP n =ᵐ[prior p N] fun ω =>
      (p.tau * p.eta + (p.tau + T p (weight p k)) * ratingStat p k n ω +
          p.eta * ∑ i, p.eta * ratingStat p k i ω / (p.eta + weight p k i)) /
        ((p.eta + weight p k n) * (p.tau + T p (weight p k))) := by sorry

end ReviewProvision
