-- Prove2me | Theorems.Thm_RWPI_Limit_lemma_3
-- name    : RWPI.Limit.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:11:06.567987+00:00
-- url     : https://prove2.me/theorems/2b7e5fea-50a6-42c3-b981-ca5a09cb569b
-- title:
--   Lemma 3 — uniform law of large numbers for $\frac1n\sum_i\|\zeta^T Dh(W_i)\|_p^{\rho/(\rho-1)}I(\|W_i\|_p\le c_0)$
-- statement:
--   Let $W, W_1, W_2, \dots$ be i.i.d. random vectors in $\mathbb R^m$, let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ and $\theta_* \in \mathbb R^l$ with $h(\cdot, \theta_*)$ continuously differentiable, $Dh = D_w h(\cdot, \theta_*)$, let $\rho > 1$, and let $p$ be the exponent conjugate to $q \in (1, \infty]$. Then for any $b > 0$ and $c_0 \in (0, \infty)$,
--
--   $$
--   \frac1n \sum_{i=1}^n \big\|\zeta^T Dh(W_i)\big\|_p^{\rho/(\rho-1)} I\big(\|W_i\|_p \le c_0\big) \;\longrightarrow\; \mathbb E\Big[ \big\|\zeta^T Dh(W)\big\|_p^{\rho/(\rho-1)} I\big(\|W\|_p \le c_0\big) \Big]
--   $$
--
--   uniformly over $\|\zeta\|_p \le b$, in probability, as $n \to \infty$: for every $\varepsilon > 0$, the probability that some $\zeta$ with $\|\zeta\|_p \le b$ has the two sides more than $\varepsilon$ apart tends to $0$.
--
--   This uniform law of large numbers identifies the limit of the localized penalty in the proof of Theorem 3.
--
--   **Formalization Note.** The samples are $W_0, W_1, \dots$, i.i.d. with the law of $W_0$, and the $n$-th average uses $W_0, \dots, W_{n-1}$. The probability is the outer measure of the event, so no measurability is assumed. $\|W_i\|_p$ is the $\ell_p$ norm on $\mathbb R^m$, as printed. The page does not repeat the standing assumptions; $\rho > 1$ (needed for the exponent $\rho/(\rho-1)$), the continuous differentiability of $h(\cdot,\theta_*)$ (A3)), the conjugate exponents (A1)) and the i.i.d. sampling are stated explicitly.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 34, App. A.3, Lemma 3 (proof pp. 34–35)

import Mathlib
import Definitions.Def_RWPI_Limit_rowNorm

open MeasureTheory ProbabilityTheory Filter Topology

namespace RWPI.Limit

/-- Lemma 3 (Blanchet, Kang & Murthy, arXiv:1610.05627v4, App. A.3, p. 34): a uniform law of large
numbers. For i.i.d. `W_0, W_1, …` in `ℝ^m`, `ρ > 1`, `h(·, θ*)` continuously differentiable,
`b > 0` and `c₀ ∈ (0, ∞)`,
`(1/n) Σ_{i<n} ‖ζ^T Dh(W_i)‖_p^{ρ/(ρ−1)} I(‖W_i‖_p ≤ c₀) → E[‖ζ^T Dh(W)‖_p^{ρ/(ρ−1)} I(‖W‖_p ≤ c₀)]`
uniformly over `‖ζ‖_p ≤ b`, in probability. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 < ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (b c₀ : ℝ) (hb : 0 < b) (hc₀ : 0 < c₀) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => μ {ω | ∃ ζ : Fin r → ℝ, ‖WithLp.toLp p ζ‖ ≤ b ∧
      ε < |(1 / (n : ℝ)) * ∑ i : Fin n,
              (if ‖WithLp.toLp p (W i ω)‖ ≤ c₀
                then rowNorm p h θs ζ (W i ω) ^ (ρ / (ρ - 1)) else 0)
            - ∫ ω', (if ‖WithLp.toLp p (W 0 ω')‖ ≤ c₀
                then rowNorm p h θs ζ (W 0 ω') ^ (ρ / (ρ - 1)) else 0) ∂μ|}) atTop (𝓝 0) := by sorry

end RWPI.Limit
