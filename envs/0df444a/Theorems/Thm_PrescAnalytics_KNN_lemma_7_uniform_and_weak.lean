-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_lemma_7_uniform_and_weak
-- name    : PrescAnalytics.KNN.lemma_7_uniform_and_weak
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:42:34.868831+00:00
-- url     : https://prove2.me/theorems/404a82ab-a39a-4bfb-b06a-627d20c8af65
-- title:
--   Lemma 7 — from fixed-z and fixed-D convergence to simultaneous convergence in z and weak convergence of μ̂_{Y|x,N}
-- statement:
--   Let $w_{N,i}(x)$ be data-dependent weights that, almost surely and for $\mu_X$-almost every $x$, are nonnegative and sum to one for all large $N$, so that $\hat\mu_{Y|x,N}=\sum_{i=1}^N w_{N,i}(x)\,\delta_{y^i}$ is a probability measure. Let $\mathcal Y$ be a measurable set containing $Y$ and every observation $y^i$ almost surely. Suppose that $c(z;y)$ is equicontinuous in $z$ (Assumption 4), that
--
--   1. for each fixed $z\in\mathcal Z$, $\widehat C_N(z\mid x)\to C(z\mid x)$ almost surely, for $\mu_X$-a.e. $x$; and
--   2. for each fixed measurable $D\subseteq\mathcal Y$, $\hat\mu_{Y|x,N}(D)\to\mu_{Y|x}(D)$ almost surely, for $\mu_X$-a.e. $x$.
--
--   Then, almost surely, for $\mu_X$-a.e. $x$,
--   $$\widehat C_N(z\mid x)\to C(z\mid x)\ \text{ for all } z\in\mathcal Z,\qquad\text{and}\qquad \int f\,d\hat\mu_{Y|x,N}\to\int f\,d\mu_{Y|x}\ \text{ for every bounded continuous } f.$$
--
--   The point is the exchange of quantifiers: the hypotheses hold off a null set that may depend on $z$ and on $D$, while the conclusion holds off a single null set, simultaneously for all $z$ and with weak convergence. In the proof of Theorem 15 this lemma turns the two applications of Walk's theorem into the hypotheses of Lemma 6.
--
--   **Formalization Note** The paper writes the lemma for arbitrary weights; its notation $\mathbb E_{\hat\mu_{Y|x,N}}$ presupposes that they are nonnegative and sum to $1$, and the lemma is false for signed weights of unbounded total variation, so this is a hypothesis here (kNN weights satisfy it for $N\ge2$). Weak convergence $\hat\mu_{Y|x,N}\to\mu_{Y|x}$ is stated through its definition, convergence of integrals of every bounded continuous $f$, with $\int f\,d\hat\mu_{Y|x,N}=\sum_i w_{N,i}(x)f(y^i)$. The paper's set $\mathcal Y$ appears explicitly: equicontinuity is required on $\mathcal Y$, the observations lie in $\mathcal Y$ almost surely, $Y\in\mathcal Y$ $\mu$-a.s., and $\mathcal Y$ is taken measurable so that $D\subseteq\mathcal Y$ ranges over enough sets. $\mu_{Y|x}$ is `μ.condKernel x`; quantifier order "almost surely, for $\mu_X$-a.e. $x$".
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 47, Lemma 7

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- **Lemma 7** (arXiv:1402.5481v4, p. 47), for data-dependent weights `w N i ω x = w_{N,i}(x)` that
are eventually nonnegative and sum to 1. If `c(z; y)` is equicontinuous in `z` (Assumption 4), for
each fixed `z ∈ 𝒵`, `Ĉ_N(z|x) → C(z|x)` a.s. for `μ_X`-a.e. `x`, and for each fixed measurable
`D ⊆ 𝒴`, `μ̂_{Y|x,N}(D) → μ_{Y|x}(D)` a.s. for `μ_X`-a.e. `x`, then a.s., for `μ_X`-a.e. `x`,
`Ĉ_N(z|x) → C(z|x)` for all `z ∈ 𝒵` simultaneously and `μ̂_{Y|x,N} → μ_{Y|x}` weakly (tested
against every bounded continuous function). -/
theorem lemma_7_uniform_and_weak
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hYs_meas : MeasurableSet Ys) (hYs : ∀ᵐ p ∂μ, p.2 ∈ Ys)
    (w : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin dx) → ℝ)
    (ys : ℕ → Ω → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ᵐ ω ∂P, ∀ i, ys i ω ∈ Ys)
    (hw : ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst), ∀ᶠ N in atTop,
      (∀ i < N, 0 ≤ w N i ω x) ∧ ∑ i ∈ Finset.range N, w N i ω x = 1)
    (h4 : Assumption4 c Z Ys)
    (hC : ∀ z ∈ Z, ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
      Tendsto (fun N => weightedCost c (fun N i => w N i ω x) (fun i => ys i ω) N z) atTop
        (𝓝 (condCost μ c z x)))
    (hD : ∀ D ⊆ Ys, MeasurableSet D → ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
      Tendsto (fun N => weightedMeasure (fun N i => w N i ω x) (fun i => ys i ω) N D) atTop
        (𝓝 (μ.condKernel x D).toReal)) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
      (∀ z ∈ Z, Tendsto (fun N => weightedCost c (fun N i => w N i ω x) (fun i => ys i ω) N z)
        atTop (𝓝 (condCost μ c z x))) ∧
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin dy)) ℝ,
        Tendsto (fun N => weightedMean (fun N i => w N i ω x) (fun i => ys i ω) f N) atTop
          (𝓝 (∫ y, f y ∂(μ.condKernel x))) := by sorry

end PrescAnalytics.KNN
