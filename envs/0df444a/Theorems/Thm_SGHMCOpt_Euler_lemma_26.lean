-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_26
-- name    : SGHMCOpt.Euler.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:17.324825+00:00
-- url     : https://prove2.me/theorems/9df5025f-64e7-4971-b397-7bd7dce56fe5
-- title:
--   Lemma 26, p. 69 — |∫G dμ − ∫G dν| ≤ (c₁σ + c₂)𝒲₂(μ,ν) for C¹ functions G with ‖∇G(w)‖ ≤ c₁‖w‖ + c₂
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R^{2d}$ (with the Euclidean norm) with finite second moments, and let $G:\mathbb R^{2d}\to\mathbb R$ be a $C^1$ function with
--   $$\|\nabla G(w)\|\le c_1\|w\|+c_2\qquad(w\in\mathbb R^{2d})$$
--   for constants $c_1>0$, $c_2\ge0$. Then $G$ is integrable under both measures and
--   $$\Big|\int G\,d\mu-\int G\,d\nu\Big|\le(c_1\sigma+c_2)\,\mathcal W_2(\mu,\nu),\qquad \sigma^2=\max\Big\{\int\|w\|^2\mu(dw),\int\|w\|^2\nu(dw)\Big\}.$$
--
--   This is the continuity of expectations of quadratically growing functions in the 2-Wasserstein distance (Polyanskiy–Wu 2016); the paper applies it to $G(x,v)=F_z(x)$ with $c_1=M$, $c_2=B$.
--
--   **Formalization Note** $\mathbb R^{2d}$ is `WithLp 2 (ℝ^d × ℝ^d)`, the product with the Euclidean norm, so that $\|w\|$, $\nabla G$ and the cost of $\mathcal W_2$ are the Euclidean ones. Integrability of $G$ is part of the conclusion.
-- source:
--   arXiv:1809.04618v4, Lemma 26, p. 69 (citing Polyanskiy, Wu 2016)

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Transport

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Lemma 26, p. 69 (PW16): for probability measures `μ, ν` on `ℝ^{2d}` (Euclidean norm) with
finite second moments and a `C¹` function `G` with `‖∇G(w)‖ ≤ c₁‖w‖ + c₂`, `c₁ > 0`, `c₂ ≥ 0`,
`|∫ G dμ − ∫ G dν| ≤ (c₁σ + c₂) 𝒲₂(μ, ν)` with `σ² = max{∫‖w‖² dμ, ∫‖w‖² dν}`. -/
theorem lemma_26 {d : ℕ} (μ ν : Measure (Phase d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun w => ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w => ‖w‖ ^ 2) ν) (G : Phase d → ℝ) (c1 c2 : ℝ) (hG : ContDiff ℝ 1 G)
    (hgrad : ∀ w, ‖gradient G w‖ ≤ c1 * ‖w‖ + c2) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) :
    Integrable G μ ∧ Integrable G ν ∧
      |∫ w, G w ∂μ - ∫ w, G w ∂ν| ≤
        (c1 * Real.sqrt (max (∫ w, ‖w‖ ^ 2 ∂μ) (∫ w, ‖w‖ ^ 2 ∂ν)) + c2) * W2 μ ν := by sorry

end SGHMCOpt.Euler
