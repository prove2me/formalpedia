-- Prove2me | Theorems.Thm_RWPI_Limit_asymptotic_upper_bound
-- name    : RWPI.Limit.asymptotic_upper_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-13T20:36:57.095196+00:00
-- url     : https://prove2.me/theorems/9901de6e-1e0f-4f40-8034-0400bad2493d
-- title:
--   The asymptotic stochastic upper bound in RWPI Theorem 3
-- statement:
--   Let $W_0,W_1,\ldots$ be independent, identically distributed measurable random vectors in $\mathbb R^m$. Fix $\theta_*$ and let $h(\cdot,\theta_*):\mathbb R^m\to\mathbb R^r$ be continuously differentiable. Assume $\rho\ge1$, $1<q\le\infty$, and $1/p+1/q=1$. Suppose $h(W_0,\theta_*)$ is integrable, has mean zero, and has finite second moment. Assume also that for every nonzero $\zeta\in\mathbb R^r$,
--   $$
--   \mathbb P\!\left(\|\zeta^T D_wh(W_0,\theta_*)\|_p>0\right)>0.
--   $$
--   Let $R_n$ be the robust Wasserstein profile of the empirical distribution of $W_0,\ldots,W_{n-1}$ with transportation cost $\|u-w\|_q^\rho$. Let $H$ be the centered Gaussian vector with covariance $\mathbb E[h(W_0,\theta_*)h(W_0,\theta_*)^T]$, and let $\bar R(H)$ be the limiting variational functional defined in Theorem 3. Then for every bounded, continuous, nondecreasing $f:\mathbb R\to\mathbb R$,
--   $$
--   \limsup_{n\to\infty}\mathbb E\!\left[f\!\left(n^{\rho/2}R_n\right)\right]
--   \le \mathbb E\!\left[f\!\left(\bar R(H)\right)\right].
--   $$
--   This is the asymptotic comparison clause of Theorem 3; finiteness, measurability, and attainment are separate clauses of that theorem. The formal statement uses the real-valued conversions of the extended-real profile and limiting functional, exactly as in the parent statement.
-- source:
--   Blanchet, Kang and Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, Theorem 3, p.15; proof in Appendix A.3, pp.32–37. https://arxiv.org/abs/1610.05627v4

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_RWPI_Limit_rowNorm
import Definitions.Def_RWPI_Limit_Rbar
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution

open MeasureTheory ProbabilityTheory Filter

namespace RWPI.Limit

theorem asymptotic_upper_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
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
    (∀ f : ℝ → ℝ, Continuous f → Monotone f → (∃ C : ℝ, ∀ t, |f t| ≤ C) →
      limsup (fun n : ℕ => ∫ ω, f ((n : ℝ) ^ (ρ / 2) * (rwp (costQ q ρ) h θs
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω))).toReal) ∂μ)
        atTop
      ≤ ∫ x, f (Rbar μ (W 0) p h θs ρ x).toReal ∂(multivariateGaussian 0 (covMatrix μ (W 0) h θs))) := by sorry

end RWPI.Limit
