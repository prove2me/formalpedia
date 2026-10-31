-- Prove2me | Theorems.Thm_ReviewProvision_eq_6
-- name    : ReviewProvision.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:12.657762+00:00
-- url     : https://prove2.me/theorems/0378558b-cf52-4321-b115-b7dbcf140527
-- title:
--   Eq. (6), p.15 — the profit as a truncated Gaussian integral
-- statement:
--   For a policy $\psi$ and feasible sales $\vec k$, write $\sigma_{\psi n}^2=\mathrm{Var}[v_{\psi n}]$. Then
--
--   $$
--   \Pi_\psi(\vec k)=\sum_{n=1}^N\left[\frac{k_n(1-k_n)}{h}+\frac m{4h}\,\Pi_2(\sigma_{\psi n})\right],
--   $$
--
--   where $\Pi_2(0)=1$ and, for $\sigma>0$,
--
--   $$
--   \frac m{4h}\,\Pi_2(\sigma)=\int_{-1/\sigma}^{+\infty}\frac{m(z\sigma+1)^2}{4h}\,\phi(z)\,dz .
--   $$
--
--   The firm's problem therefore depends on the information policy only through the variances of the customer evaluations.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - generalization: (6) for ψ ∈ {A, G}, as an equality of the two maximization problems → the identity of the two objectives at every feasible ~k, for all four policies; reason: the pointwise identity implies the equality of the maxima, and FP and JP use it on p.45
--   - encoding: the integral of (6) with lower limit −1/σ_{ψn} → Π_2(σ) with Π_2(0) = 1, equal to the integral for σ > 0; reason: at σ = 0 the lower limit is undefined; this happens when the reviews carry no information about the value of cluster n, such as at k_n = 0 under AP
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (6), p.15

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (6)**, SSRN 3403322 (manuscript of 2021-05-24), p.15 (PDF 15): for a policy `ψ` and feasible
sales, with `σ_{ψn}² = Var[v_{ψn}]`,
`Π_ψ(~k) = Σ_n [k_n(1 − k_n)/h + (m/(4h)) Π_2(σ_{ψn})]`, where `Π_2(0) = 1` and, for `σ > 0`,
`(m/(4h)) Π_2(σ) = ∫_{−1/σ}^{∞} m(zσ + 1)²/(4h) φ(z) dz`.

**Formalization Note.** The integral of (6) is undefined at `σ = 0`, which occurs at `k_n = 0`; `Pi2`
is the value there. -/
theorem eq_6 (p : Params) {N : ℕ} (ψ : Policy) (k : Fin N → ℝ) (hk : Feasible k) :
    profit p ψ k = ∑ n, (k n * (1 - k n) / p.h +
      p.m / (4 * p.h) * Pi2 √(Var[posteriorMean p k ψ n; prior p N])) ∧
    Pi2 0 = 1 ∧
    ∀ σ : ℝ, 0 < σ →
      p.m / (4 * p.h) * Pi2 σ =
        ∫ z in Set.Ioi (-1 / σ), p.m * (z * σ + 1) ^ 2 / (4 * p.h) * phi z := by sorry

end ReviewProvision
