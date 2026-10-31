-- Prove2me | Theorems.Thm_ReviewProvision_eq_1
-- name    : ReviewProvision.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:55.231989+00:00
-- url     : https://prove2.me/theorems/59df118f-8389-4925-942b-014c598c5942
-- title:
--   Eq. (1), p.11 — posterior mean under AP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales and every cluster $n$, the customer evaluation under AP satisfies, almost surely,
--
--   $$
--   v_{An}=\frac{\tau\eta+(\tau+\eta)\,y_n}{\tau\eta+(\tau+\eta)\,w_n}.
--   $$
--
--   This is the Bayes update of the cluster value given the cluster's own rating.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: (1) with q_p and w_n r_n → the statistic y_n = w_n(q + t_n) + √w_n ε_n, with q_p = 1; reason: y_n = w_n r_n generates the same information when w_n > 0 and is 0 when no ratings exist; q_p = 1 as in §3.1
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (1), p.11

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (1)**, SSRN 3403322 (manuscript of 2021-05-24), p.11 (PDF 11): the AP posterior mean, with
`q_p = 1` and `w_n r_n = y_n`:
`v_{An} = (τη + (τ+η) y_n)/(τη + (τ+η) w_n)` almost surely.

**Formalization Note.** Written with the statistic `y_n`, the formula holds at `k_n = 0` too, where
`y_n = 0` and `v_{An} = 1`. -/
theorem eq_1 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) (n : Fin N) :
    posteriorMean p k .AP n =ᵐ[prior p N] fun ω =>
      (p.tau * p.eta + (p.tau + p.eta) * ratingStat p k n ω) /
        (p.tau * p.eta + (p.tau + p.eta) * weight p k n) := by sorry

end ReviewProvision
