-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_theorem_5_knn_unbounded_case
-- name    : PrescAnalytics.KNN.theorem_5_knn_unbounded_case
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T03:17:39.50982+00:00
-- url     : https://prove2.me/theorems/bcdae7b2-e713-4cd2-90e1-7d3df579c90f
-- title:
--   Theorem 5 (kNN), case 2 of Assumption 5 — asymptotic optimality and consistency for unbounded feasible sets
-- statement:
--   Let $(x^1,y^1),(x^2,y^2),\dots$ be independent and identically distributed with law $\mu$ of $(X,Y)$ on $\mathbb R^{d_x}\times\mathbb R^{d_y}$, with $X\in\mathcal X$ and $Y\in\mathcal Y$ almost surely. Let $c:\mathbb R^{d_z}\times\mathbb R^{d_y}\to\mathbb R$ be a cost and $\mathcal Z\subseteq\mathbb R^{d_z}$ a feasible set satisfying Assumption 3 (existence) and Assumption 4 (equicontinuity of $c(z;y)$ in $z$, uniformly over $y\in\mathcal Y$), and **case 2 of Assumption 5**:
--
--   1. $\mathcal Z$ is closed and nonempty;
--   2. $\liminf_{\|z\|\to\infty}\inf_{y\in\mathcal Y} c(z;y)>-\infty$;
--   3. for every $x\in\mathcal X$ there is a measurable $D_x\subseteq\mathcal Y$ with $\mu_{Y|x}(D_x)>0$ such that $c(z;y)\to\infty$ as $\|z\|\to\infty$, uniformly over $y\in D_x$.
--
--   Let $w_{N,i}(x)$ be the kNN weights (12) with
--   $$k=\min\big\{\lceil CN^\delta\rceil,\ N-1\big\},\qquad C>0,\ 0<\delta<1,$$
--   and let $\hat z_N(x)\in\arg\min_{z\in\mathcal Z}\sum_{i=1}^N w_{N,i}(x)\,c(z;y^i)$ as in (3). Then $\hat z_N(x)$ is asymptotically optimal and consistent: with probability 1, for $\mu_X$-almost every $x$,
--   $$\lim_{N\to\infty}\mathbb E\big[c(\hat z_N(x);Y)\mid X=x\big]=v^*(x)\qquad\text{and}\qquad \lim_{N\to\infty}\ \inf_{z\in\mathcal Z^*(x)}\|\hat z_N(x)-z\|=0 .$$
--
--   This is the unbounded-feasible-set half of Theorem 5 (e.g. the newsvendor with $\mathcal Z=[0,\infty)$); the bounded half (case 1 of Assumption 5) follows from the Walk (2010) step and Lemma 6, so Theorem 5 is the conjunction of the two cases.
--
--   **Formalization Note** Identical to `PrescAnalytics.KNN.theorem_5_knn_asymptotically_optimal`, with the hypothesis `Assumption5` replaced by its second disjunct written out (`IsClosed Z`, `Z.Nonempty`, `CostBoundedBelowAtInfinity c Z Ys`, and the per-$x$ coercivity sets read in the version `μ.condKernel x`). The conclusion is Definition 1 for every selection from the argmin, inside the almost-sure quantifiers, exactly as in the parent theorem.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 19, Theorem 5 with Assumption 5 case 2 (pp. 18-19); restated with iid sampling as Theorem 15, p. 43; proof p. 47 (via Lemmas 5-7, pp. 45-47)

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- **Theorem 5 (kNN) under case 2 of Assumption 5** (= Theorem 15, iid case, arXiv:1402.5481v4,
pp. 19, 43, 47). Under Assumptions 3 and 4, with `𝒵` closed and nonempty,
`liminf_{‖z‖→∞} inf_{y ∈ 𝒴} c(z; y) > -∞`, and for every `x ∈ 𝒳` a measurable `D_x ⊆ 𝒴` with
`μ_{Y|x}(D_x) > 0` on which `c(z; y) → ∞` as `‖z‖ → ∞` uniformly (case 2 of Assumption 5), and iid
data `(x^i, y^i) ~ μ`, the kNN predictive prescription with `k = min {⌈C N^δ⌉, N - 1}`, `C > 0`,
`0 < δ < 1`, is asymptotically optimal and consistent (Definition 1), for every selection from its
argmin. -/
theorem theorem_5_knn_unbounded_case
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS_meas : ∀ i, Measurable (S i)) (hS_indep : iIndepFun S P)
    (hS_law : ∀ i, P.map (S i) = μ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (Xs : Set (EuclideanSpace ℝ (Fin dx))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hXs : ∀ᵐ p ∂μ, p.1 ∈ Xs) (hYs : ∀ᵐ p ∂μ, p.2 ∈ Ys)
    (h3 : Assumption3 μ c Z) (h4 : Assumption4 c Z Ys)
    (hZ_closed : IsClosed Z) (hZ_ne : Z.Nonempty)
    (h5_below : CostBoundedBelowAtInfinity c Z Ys)
    (h5_coercive : ∀ x ∈ Xs, ∃ D ⊆ Ys, MeasurableSet D ∧ 0 < μ.condKernel x D ∧
      CoerciveUniformlyOn c Z D)
    (C δ : ℝ) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsAsymptoticallyOptimal P μ c Z (knnArgmin C δ c Z S) ∧
      IsConsistent P μ c Z (knnArgmin C δ c Z S) := by sorry

end PrescAnalytics.KNN
