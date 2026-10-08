-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_theorem_10
-- name    : SmithRegenerative.CLT.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:52.781775+00:00
-- url     : https://prove2.me/theorems/6f722366-5ea7-4330-94c1-669752a4939d
-- title:
--   Theorem 10 — M cumulative processes on the same regeneration points are jointly asymptotically normal with covariances a_kl, and b_kl if μ₂ < ∞
-- statement:
--   Let $w^{(1)}_t, \dots, w^{(M)}_t$ be $M$ cumulative processes based on the same renewal process $t_1, t_2, \dots$ ($t_0 = 0$, $w^{(i)}_0 = 0$), so that the cycle vectors $(t_n, y^{(1)}_n, \dots, y^{(M)}_n, \tilde y^{(1)}_n, \dots, \tilde y^{(M)}_n)$ are independent and identically distributed. Let $n_t$ be the number of regenerations in $[0,t]$. Suppose $\mu_1 = E t_1 < \infty$ and $E(\Delta_n \tilde w^{(i)}_t)^2 < \infty$ for every $i$, and put
--   $$\kappa^{(i)}_1 = E \Delta_n w^{(i)}_t, \qquad a_{kl} = \operatorname{cov}\left(\Delta_n w^{(k)}_t, \Delta_n w^{(l)}_t\right).$$
--   Then:
--
--   1. as $t \to \infty$ the random vector with components
--   $$\frac{w^{(i)}_t - \kappa^{(i)}_1 n_t}{(t/\mu_1)^{1/2}}, \qquad i = 1, \dots, M,$$
--   converges in distribution to the centred normal law with covariance matrix $(a_{kl})$;
--   2. if in addition $\mu_2 = E t_1^2 < \infty$, the random vector with components
--   $$\frac{w^{(i)}_t - (\kappa^{(i)}_1/\mu_1)\, t}{(t/\mu_1)^{1/2}}, \qquad i = 1, \dots, M,$$
--   converges in distribution to the centred normal law with covariance matrix
--   $$b_{kl} = \operatorname{cov}\left\{ \Delta_n\!\left(w^{(k)}_t - \frac{\kappa^{(k)}_1}{\mu_1} t\right), \Delta_n\!\left(w^{(l)}_t - \frac{\kappa^{(l)}_1}{\mu_1} t\right) \right\},$$
--   where $\Delta_n\left(w^{(k)}_t - (\kappa^{(k)}_1/\mu_1) t\right) = y^{(k)}_n - (\kappa^{(k)}_1/\mu_1) t_n$.
--
--   This is the multivariate central limit theorem for regenerative processes: several additive functionals of one regenerative process, observed over the same cycles, fluctuate jointly like a Gaussian vector, with covariances computed from a single cycle.
--
--   **Formalization Note** The random vectors are elements of the Euclidean space $\mathbb R^M$, and convergence is weak convergence of their laws to the Gaussian law $\mathcal N(0, a)$ (resp. $\mathcal N(0, b)$) along the real time $t \to \infty$. The matrices $a$ and $b$ are defined as covariance matrices, hence positive semidefinite; degenerate limits are allowed and no positivity is assumed. The hypothesis $a_{kl} < \infty$ of the paper follows from $E(\Delta_n \tilde w^{(i)}_t)^2 < \infty$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 30, Theorem 10

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Theorem 10, p. 30: "If `w_t^{(1)}, w_t^{(2)}, …, w_t^{(M)}` are M-cumulative
processes (based on the same sequence of regeneration points); if `μ₁ < ∞`, `E(Δ_n w̃_t^{(i)})² < ∞`,
and if `κ₁^{(i)} = EΔ_n w_t^{(i)}`, `a_kl = cov(Δ_n w_t^{(k)}, Δ_n w_t^{(l)}) < ∞`, for all `k, l` then
the random variables `(w_t^{(i)} − κ₁^{(i)} n_t)/(t/μ₁)^{1/2}` tend, as `t → ∞`, to be jointly
normally distributed with covariance matrix `a_kl`. If, in addition, `μ₂ < ∞`, then the random
variables `(w_t^{(i)} − (κ₁^{(i)}/μ₁)t)/(t/μ₁)^{1/2}` tend, as `t → ∞`, to be jointly normally
distributed with covariance matrix
`b_kl = cov{Δ_n(w_t^{(k)} − (κ₁^{(k)}/μ₁)t), Δ_n(w_t^{(l)} − (κ₁^{(l)}/μ₁)t)}`."

**Formalization Note** The `M` processes are `w i`, `i : Fin M`, on the common renewal process
`τ` (`t₀ = 0`, `w₀ = 0`), with i.i.d. cycle vectors (`IsCumulativeModel`). The random vectors
live in `EuclideanSpace ℝ (Fin M)`; "jointly normally distributed with covariance matrix `a`" is
convergence in distribution, along real `t → ∞`, to `multivariateGaussian 0 a`. `a` and `b` are
defined as covariance matrices (of `y₁^{(k)}`, resp. of `y₁^{(k)} − (κ₁^{(k)}/μ₁) t₁`, which is
`Δ_n(w^{(k)} − (κ₁^{(k)}/μ₁)t)`), so they are positive semidefinite and the limits are genuine,
possibly degenerate, Gaussian laws; no positivity is assumed. `E(Δ_n w̃^{(i)})² < ∞` is
integrability of `(ỹ₁^{(i)})²`; it makes every `a_kl` finite. `(t/μ₁)^{1/2}` is
`Real.sqrt (t / μ₁)`, and `n_t` is `count`. -/
theorem theorem_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℕ} (τ : ℕ → Ω → ℝ) (w : Fin M → ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ w)
    (hμ : Integrable (τ 1) P)
    (hvar2 : ∀ i, Integrable (fun ω => varIncr (w i) τ 1 ω ^ 2) P) :
    TendstoInDistribution
      (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
        (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          Real.sqrt (t / mu1 P τ)))
      atTop id (fun _ => P)
      (multivariateGaussian 0 (covMatrix P (fun k => incr (w k) τ 1))) ∧
    (Integrable (fun ω => τ 1 ω ^ 2) P →
      TendstoInDistribution
        (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
          (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) / mu1 P τ * t) / Real.sqrt (t / mu1 P τ)))
        atTop id (fun _ => P)
        (multivariateGaussian 0 (covMatrix P (fun k ω =>
          incr (w k) τ 1 ω - (∫ ω', incr (w k) τ 1 ω' ∂P) / mu1 P τ * τ 1 ω)))) := by sorry

end SmithRegenerative.CLT
