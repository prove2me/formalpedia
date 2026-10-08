-- Prove2me | Theorems.Thm_RWPI_Limit_theorem_3
-- name    : RWPI.Limit.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:29:06.291281+00:00
-- url     : https://prove2.me/theorems/5508c23e-a0ef-434b-972f-1f51680422c6
-- title:
--   Theorem 3 — $n^{\rho/2}R_n(\theta_*;\rho) \lesssim_D \bar R(\rho)$: asymptotic stochastic upper bound for the RWP function
-- statement:
--   Let $W, W_1, W_2, \dots$ be i.i.d. random vectors in $\mathbb R^m$, let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ and $\theta_* \in \mathbb R^l$. For $n \ge 1$ let $R_n(\theta_*) = \inf\{D_c(P, \mathbb P_n) : \mathbb E_P[h(W, \theta_*)] = \mathbf 0\}$ be the RWP function of the empirical distribution $\mathbb P_n$ of $W_1, \dots, W_n$. Assume:
--
--   1. (A1) $c(u, w) = \|u - w\|_q^\rho$ with $\rho \ge 1$ and $q \in (1, \infty]$, and $p$ satisfies $1/p + 1/q = 1$;
--   2. (A2) $\mathbb E[h(W, \theta_*)] = \mathbf 0$ and $\mathbb E\|h(W, \theta_*)\|_2^2 < \infty$;
--   3. (A3) $h(\cdot, \theta_*)$ is continuously differentiable with derivative $D_w h(\cdot, \theta_*)$;
--   4. (A4) for each $\zeta \in \mathbb R^r$ with $\zeta \ne 0$, $\mathbb P\big(\|\zeta^T D_w h(W, \theta_*)\|_p > 0\big) > 0$.
--
--   Let $H \sim \mathcal N\big(\mathbf 0, \mathrm{Cov}[h(W, \theta_*)]\big)$ with $\mathrm{Cov}[h(W,\theta_*)] = \mathbb E[h(W, \theta_*) h(W, \theta_*)^T]$, and define, for $\rho > 1$,
--   $$
--   \bar R(\rho) = \max_{\zeta \in \mathbb R^r} \Big\{ \rho \zeta^T H - (\rho - 1)\, \mathbb E\big\|\zeta^T D_w h(W, \theta_*)\big\|_p^{\rho/(\rho-1)} \Big\},
--   $$
--   and for $\rho = 1$,
--   $$
--   \bar R(1) = \max_{\zeta :\ \mathbb P(\|\zeta^T D_w h(W, \theta_*)\|_p > 1) = 0} \zeta^T H .
--   $$
--   Then $n^{\rho/2} R_n(\theta_*; \rho) \lesssim_D \bar R(\rho)$ as $n \to \infty$; that is, for every continuous, bounded and non-decreasing $f : \mathbb R \to \mathbb R$,
--
--   $$
--   \limsup_{n \to \infty} \mathbb E\Big[ f\big(n^{\rho/2} R_n(\theta_*; \rho)\big) \Big] \le \mathbb E\big[ f(\bar R(\rho)) \big] .
--   $$
--
--   In addition, $R_n(\theta_*)$ is finite for every $n \ge 1$ and every sample, it is a measurable function of the sample (up to null sets), and the maxima defining $\bar R(\rho)$ are attained for every value of $H$.
--
--   This is the paper's main theorem. It gives the rate $n^{-\rho/2}$ at which the RWP function at the true parameter goes to zero, and an explicit stochastic bound for its rescaled limit; its quantiles calibrate the radius of Wasserstein distributionally robust estimators and RWP confidence regions.
--
--   **Formalization Note.** The samples are $W_0, W_1, \dots$, independent and identically distributed with the law of $W_0$ (which plays the role of $W$), and $R_n$ uses $W_0, \dots, W_{n-1}$. $R_n$ takes values in $[0, \infty]$; the finiteness clause guarantees that converting it to a real number loses nothing, and the measurability clause guarantees that $\mathbb E[f(n^{\rho/2}R_n)]$ is a genuine expectation (both are facts the paper uses implicitly). $\bar R(\rho)$ is computed in the extended reals with the moment $\mathbb E\|\cdot\|_p^{\rho/(\rho-1)}$ in $[0, \infty]$; the attainment clause makes it a finite maximum before $f$ is applied. $H$'s law is Mathlib's `multivariateGaussian 0 Cov` on Euclidean $\mathbb R^r$; $\mathrm{Cov}$ is positive semidefinite under A2). The paper's A1) says $q \ge 1$, while (17) and the proof (p. 33) use $q \in (1, \infty]$; the latter is used. Distinct samples are not assumed.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 15, Assumptions A1)–A4), definition of ≲_D and Theorem 3 (proof App. A.3, pp. 32–37)

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_RWPI_Limit_rowNorm
import Definitions.Def_RWPI_Limit_Rbar
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution

open MeasureTheory ProbabilityTheory Filter

namespace RWPI.Limit

/-- Theorem 3 (Blanchet, Kang & Murthy, arXiv:1610.05627v4, p. 15): the asymptotic stochastic
upper bound `n^{ρ/2} R_n(θ*; ρ) ≲_D R̄(ρ)`. `W_0, W_1, …` are i.i.d. random vectors in `ℝ^m`
(`W_0` plays the role of `W`), `R_n(θ*)` is the RWP function (16) of the empirical distribution of
`W_0, …, W_{n−1}` with the cost `c(u, w) = ‖w − u‖_q^ρ`. Under A1) (`ρ ≥ 1`, `q ∈ (1, ∞]`,
`1/p + 1/q = 1`), A2), A3) and A4), the conclusion has four parts:
1. `R_n(θ*) < ∞` for every `n ≥ 1` and every outcome;
2. `R_n(θ*)` is a.e.-measurable for every `n`;
3. the supremum defining `R̄(ρ)` at `H = x` is attained for every `x ∈ ℝ^r`;
4. for every continuous, bounded, non-decreasing `f : ℝ → ℝ`,
   `limsup_n E[f(n^{ρ/2} R_n(θ*))] ≤ E[f(R̄(ρ))]`, where `H ∼ 𝒩(0, E[h(W, θ*) h(W, θ*)^T])`. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    -- A1)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    -- A2)
    (hint : Integrable (fun ω => h (W 0 ω) θs) μ) (hmean : ∫ ω, h (W 0 ω) θs ∂μ = 0)
    (hL2 : MemLp (fun ω => h (W 0 ω) θs) 2 μ)
    -- A3)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    -- A4)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W 0 ω)}) :
    (∀ n : ℕ, 1 ≤ n → ∀ ω, rwp (costQ q ρ) h θs
        (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω)) < ⊤) ∧
    (∀ n : ℕ, AEMeasurable (fun ω => rwp (costQ q ρ) h θs
        (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω))) μ) ∧
    (∀ x : EuclideanSpace ℝ (Fin r), ∃ ζ₀ ∈ RbarFeasible μ (W 0) p h θs ρ,
        RbarObjective μ (W 0) p h θs ρ x ζ₀ = Rbar μ (W 0) p h θs ρ x) ∧
    (∀ f : ℝ → ℝ, Continuous f → Monotone f → (∃ C : ℝ, ∀ t, |f t| ≤ C) →
      limsup (fun n : ℕ => ∫ ω, f ((n : ℝ) ^ (ρ / 2) * (rwp (costQ q ρ) h θs
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω))).toReal) ∂μ)
        atTop
      ≤ ∫ x, f (Rbar μ (W 0) p h θs ρ x).toReal ∂(multivariateGaussian 0 (covMatrix μ (W 0) h θs))) := by sorry

end RWPI.Limit
