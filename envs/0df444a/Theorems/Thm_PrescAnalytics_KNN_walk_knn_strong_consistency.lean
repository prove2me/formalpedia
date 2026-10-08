-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_walk_knn_strong_consistency
-- name    : PrescAnalytics.KNN.walk_knn_strong_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:43.187984+00:00
-- url     : https://prove2.me/theorems/83f6c813-4f8c-4123-9184-5e5bbb0eee27
-- title:
--   Proof of Theorem 15 (Walk 2010 step) — kNN conditional means converge a.s. for μ_X-a.e. x
-- statement:
--   Let $(x^1,y^1),(x^2,y^2),\dots$ be independent and identically distributed with law $\mu$ on $\mathbb R^{d_x}\times\mathbb R^{d_y}$, and let $w_{N,i}(x)$ be the kNN weights (12) with $k=\min\{\lceil CN^\delta\rceil,N-1\}$ for some $C>0$ and $0<\delta<1$, ties broken by lower index first. Let $h:\mathbb R^{d_y}\to\mathbb R$ be measurable with $\mathbb E|h(Y)|<\infty$. Then, with probability 1, for $\mu_X$-almost every $x$,
--   $$\lim_{N\to\infty}\ \sum_{i=1}^N w_{N,i}(x)\,h(y^i)\;=\;\mathbb E\big[h(Y)\mid X=x\big].$$
--
--   This is the step of the proof of Theorem 15 (p. 47) that invokes Theorem 5 of Walk (2010), the universal strong pointwise consistency of nearest-neighbour regression for an integrable response. The paper applies it twice: with $h=c(z;\cdot)$ it gives $\widehat C_N(z\mid x)\to C(z\mid x)$ for each fixed $z$, and with $h=\mathbb I_D$ for a measurable $D$ it gives $\hat\mu_{Y|x,N}(D)\to\mu_{Y|x}(D)$. Both are instances of the statement above. Neither Assumption 4 nor Assumption 5 is needed.
--
--   **Formalization Note** The data are a measurable sequence `S i : Ω → ℝ^{d_x} × ℝ^{d_y}` on a probability space, mutually independent (`iIndepFun`), each with law $\mu$. $\mathbb E[h(Y)\mid X=x]$ is the integral of $h$ against the version `μ.condKernel x` of the conditional law. The paper orders the quantifiers "for $\mu_X$-a.e. $x$, a.s."; the Lean uses Definition 1's order, "almost surely in $\omega$, for $\mu_X$-a.e. $x$" (the two agree since the event is jointly measurable). Samples are indexed from $0$. For $N\le1$ the formula gives $k=0$ and all weights $0$, which does not affect the limit.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 47, proof of Theorem 15 (application of Theorem 5 of Walk (2010)); weights (12), p. 10

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- The step of the proof of Theorem 15 (arXiv:1402.5481v4, p. 47) that applies Theorem 5 of Walk
(2010): for iid data `(x^i, y^i) ~ μ`, the kNN weights (12) with `k = min {⌈C N^δ⌉, N - 1}`,
`C > 0`, `0 < δ < 1`, and any measurable `h` with `E|h(Y)| < ∞`, almost surely, for `μ_X`-a.e. `x`,
`∑_i w_{N,i}(x) h(y^i) → E[h(Y) | X = x]`. The paper uses it for `h = c(z; ·)` and `h = 𝕀_D`. -/
theorem walk_knn_strong_consistency
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS_meas : ∀ i, Measurable (S i)) (hS_indep : iIndepFun S P)
    (hS_law : ∀ i, P.map (S i) = μ)
    (C δ : ℝ) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : EuclideanSpace ℝ (Fin dy) → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable (fun p => h p.2) μ) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
      Tendsto (fun N => weightedMean (knnWeight C δ (fun i => (S i ω).1) x) (fun i => (S i ω).2) h N)
        atTop (𝓝 (∫ y, h y ∂(μ.condKernel x))) := by sorry

end PrescAnalytics.KNN
