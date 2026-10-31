-- Prove2me | Theorems.Thm_ReviewProvision_jp_posterior_mean
-- name    : ReviewProvision.jp_posterior_mean
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:04.135197+00:00
-- url     : https://prove2.me/theorems/9f537e5a-7216-4e86-ae33-568efe3e0a95
-- title:
--   First display of p.24 — posterior mean under JP
-- statement:
--   Throughout, $q\sim N(1,1/\tau)$ is the unknown quality, $t_1,\dots,t_N\sim N(0,1/\eta)$ are the cluster preferences, $\varepsilon_1,\dots,\varepsilon_N\sim N(0,1)$ are rating noises, all independent, $w_n=k_n\theta\zeta$ is the precision of the average rating of cluster $n$ at sales $k_n\ge0$, and $y_n=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n$ is the rating statistic, equal to $w_nr_n$ when $w_n>0$ and to $0$ when no ratings exist.
--
--   For feasible sales and a cluster $n$ with $S_1'=\sum_lw_l-w_n>0$, and $S_2'=\sum_lw_l^2-w_n^2$, the customer evaluation under JP satisfies, almost surely,
--
--   $$
--   v_{Jn}=\frac{\eta^2S_1'\bigl(\sum_ly_l-y_n\bigr)+\tau\eta(\eta S_1'+S_2')+[\eta(\eta S_1'+S_2'+S_1'^2)+\tau(\eta S_1'+S_2')]\,y_n}{[\tau(\eta+w_n)+\eta w_n](\eta S_1'+S_2')+\eta(\eta+w_n)S_1'^2}.
--   $$
--
--   This is the Bayes update of the cluster value given the cluster's own rating and the global average.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: the display of p.24 with q_p, w_n r_n and S′_1 r̄′ → the statistic y_n = w_n(q + t_n) + √w_n ε_n, with q_p = 1; reason: y_n = w_n r_n generates the same information when w_n > 0 and is 0 when no ratings exist; q_p = 1 as in §3.1
--   - encoding: the display for all sales → the hypothesis S′_1 > 0; reason: at S′_1 = 0 the printed r̄′ and the formula are undefined; this excludes only the undefined case
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), first display of p.24

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **The JP posterior mean**, SSRN 3403322 (manuscript of 2021-05-24), first display of p.24 (PDF 24),
with `q_p = 1`, `S′_1 r̄′ = Σ_{l≠n} y_l = Σ_l y_l − y_n` and `w_n r_n = y_n`:
`v_{Jn} = (η² S′_1 Σ_{l≠n} y_l + τη(ηS′_1 + S′_2) + [η(ηS′_1 + S′_2 + S′_1²) + τ(ηS′_1 + S′_2)] y_n) / D`
almost surely, with `D = [τ(η + w_n) + ηw_n](ηS′_1 + S′_2) + η(η + w_n) S′_1²`.

**Formalization Note.** `0 < S′_1` excludes only the points where the printed `r̄′` and the formula
are undefined (no sales in the other clusters). The rating term is `{…} r_n` of the page with
`w_n r_n` written `y_n`, so the formula stays valid at `k_n = 0`. -/
theorem jp_posterior_mean (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) (n : Fin N)
    (hS : 0 < S1' (weight p k) n) :
    posteriorMean p k .JP n =ᵐ[prior p N] fun ω =>
      (p.eta ^ 2 * S1' (weight p k) n * (∑ l, ratingStat p k l ω - ratingStat p k n ω) +
          p.tau * p.eta * (p.eta * S1' (weight p k) n + S2' (weight p k) n) +
          (p.eta * (p.eta * S1' (weight p k) n + S2' (weight p k) n + S1' (weight p k) n ^ 2) +
            p.tau * (p.eta * S1' (weight p k) n + S2' (weight p k) n)) * ratingStat p k n ω) /
        ((p.tau * (p.eta + weight p k n) + p.eta * weight p k n) *
            (p.eta * S1' (weight p k) n + S2' (weight p k) n) +
          p.eta * (p.eta + weight p k n) * S1' (weight p k) n ^ 2) := by sorry

end ReviewProvision
