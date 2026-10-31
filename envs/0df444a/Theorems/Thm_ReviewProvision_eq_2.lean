-- Prove2me | Theorems.Thm_ReviewProvision_eq_2
-- name    : ReviewProvision.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:27.025693+00:00
-- url     : https://prove2.me/theorems/73679e9c-d383-447c-9ad7-18686683f5c2
-- title:
--   Eq. (2), p.12 — posterior mean under GP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales with $S_1=\sum_lw_l>0$, $S_2=\sum_lw_l^2$ and every cluster $n$, the customer evaluation under GP satisfies, almost surely,
--
--   $$
--   v_{Gn}=\frac{\tau(\eta S_1+S_2-w_nS_1)+(\tau w_n+\eta S_1)\sum_ly_l}{\tau\eta S_1+\tau S_2+\eta S_1^2}.
--   $$
--
--   This is the Bayes update of the cluster value given the global average rating, weighted by the shares of ratings.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: (2) with q_p and S_1 r̄ → the statistic y_n = w_n(q + t_n) + √w_n ε_n, with q_p = 1; reason: y_n = w_n r_n generates the same information when w_n > 0 and is 0 when no ratings exist; q_p = 1 as in §3.1
--   - encoding: (2) for all sales → the hypothesis S_1 > 0; reason: at S_1 = 0 the formula is 0/0 and r̄ is undefined; this excludes only the undefined case
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (2), p.12

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (2)**, SSRN 3403322 (manuscript of 2021-05-24), p.12 (PDF 12): the GP posterior mean, with
`q_p = 1` and `S_1 r̄ = Σ_l y_l`:
`v_{Gn} = (τ(ηS_1 + S_2 − w_n S_1) + (τ w_n + ηS_1) Σ_l y_l)/(τηS_1 + τS_2 + ηS_1²)` almost surely.

**Formalization Note.** `0 < S_1` excludes only the point where the formula is `0/0`, i.e. no sales
at all. -/
theorem eq_2 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k)
    (hS : 0 < S1 (weight p k)) (n : Fin N) :
    posteriorMean p k .GP n =ᵐ[prior p N] fun ω =>
      (p.tau * (p.eta * S1 (weight p k) + S2 (weight p k) - weight p k n * S1 (weight p k)) +
          (p.tau * weight p k n + p.eta * S1 (weight p k)) * ∑ l, ratingStat p k l ω) /
        (p.tau * p.eta * S1 (weight p k) + p.tau * S2 (weight p k) +
          p.eta * S1 (weight p k) ^ 2) := by sorry

end ReviewProvision
