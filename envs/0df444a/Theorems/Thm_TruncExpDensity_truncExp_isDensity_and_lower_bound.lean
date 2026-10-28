-- Prove2me | Theorems.Thm_TruncExpDensity_truncExp_isDensity_and_lower_bound
-- name    : TruncExpDensity.truncExp_isDensity_and_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T06:05:53.48581+00:00
-- url     : https://prove2.me/theorems/6b455799-34c8-48b8-87fc-0d500134f2b3
-- title:
--   The truncated exponential $k e^{\alpha}\mathbf 1\{0<\alpha\le\delta\}$ is a density on $(0,1]$, with its delay bound
-- statement:
--   Let $0 \le \delta \le 1$ and $k \ge 0$ satisfy the normalization
--
--   $$
--   k\,\big(e^{\delta}-1\big) \;=\; 1 ,
--   $$
--
--   and set
--
--   $$
--   f(\alpha) \;=\; \begin{cases} k\,e^{\alpha}, & 0 < \alpha \le \delta,\\[2pt] 0, & \text{otherwise.}\end{cases}
--   $$
--
--   Then:
--
--   1. $f$ is a probability density on $(0,1]$: $f(\alpha) \ge 0$ for every $\alpha$, and $\int_0^1 f(\alpha)\,d\alpha = 1$;
--   2. for every $\eta \in [0,1]$,
--   $$
--   \int_0^{\eta} f(\alpha)\,(1+\alpha-\eta)\,d\alpha \;\le\; k\,\eta .
--   $$
--
--   Part 2 is the bound that makes a truncated exponential the right randomization in scheduling: the weight $1+\alpha-\eta$ is how much a job whose $\alpha$-point is $\alpha$ delays a job with threshold $\eta$, and the bound says the expected delay grows no faster than linearly in $\eta$ with slope exactly the scale $k$.
--
--   Both densities used by Goemans, Queyranne, Schulz, Skutella and Wang — $f(\alpha)=(c-1)e^{\alpha}$ on $(0,\delta]$ with $\delta = 1-\gamma^2/(1+\gamma)$ for the common-$\alpha$ schedule of Theorem 3.5, and $g(\alpha)=(c-1)e^{\alpha}$ on $(0,\delta]$ with $\delta = \gamma + \ln(2-\gamma)$ for the per-job schedule of Theorem 3.9 — are instances of this one statement, with $k = c-1$ in both cases. Any other randomized $\alpha$-schedule built from a truncated exponential can reuse it the same way.
--
--   **Formalization Note** The density is written inline as `if 0 < a ∧ a ≤ δ then k * Real.exp a else 0`, so the statement applies to any platform definition that unfolds to this shape. The hypotheses $\delta \ge 0$ and $k \ge 0$ are stated explicitly even though the normalization already forces $\delta > 0$ and $k > 0$.
-- source:
--   The density properties established inside the proofs of Lemma 3.6 (p. 183) and Lemma 3.11 (p. 185) of Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002) 165-192, DOI 10.1137/S089548019936223X; stated here once for a general truncation point $\delta$ and scale $k$.

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

theorem TruncExpDensity.truncExp_isDensity_and_lower_bound (δ k : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hk : 0 ≤ k) (hnorm : k*(Real.exp δ-1)=1) :
    ((∀ a,0 ≤ if 0 < a ∧ a ≤ δ then k*Real.exp a else 0) ∧
      (∫ a in (0 : ℝ)..1,if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)=1) ∧
      ∀ η ∈ Icc (0 : ℝ) 1,
        (∫ a in (0 : ℝ)..η,(if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1+a-η)) ≤ k*η := by sorry
