-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_lemma_6_bounded_case
-- name    : PrescAnalytics.KNN.lemma_6_bounded_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:42:04.357338+00:00
-- url     : https://prove2.me/theorems/d8928788-d927-4865-aa36-e8ff946cf512
-- title:
--   Lemma 6 (case 1: 𝒵 bounded) — minima and minimizers of Ĉ_N(·|x) converge to v*(x) and 𝒵*(x)
-- statement:
--   Fix a covariate value $x$ and one sample path of data: weights $w_{N,i}$ that are nonnegative and sum to $1$ for all large $N$, and observations $y^i\in\mathcal Y$. Let $\mathcal Z\subseteq\mathbb R^{d_z}$ be closed, bounded and nonempty. Suppose $c(z;\cdot)$ is $\mu_{Y|x}$-integrable for every $z\in\mathcal Z$, $c$ is equicontinuous in $z$ (Assumption 4), $\mu_{Y|x}(\mathcal Y)=1$, and $\widehat C_N(z\mid x)\to C(z\mid x)$ for every $z\in\mathcal Z$. Then $\mathcal Z^*(x)\ne\emptyset$, $\arg\min_{z\in\mathcal Z}\widehat C_N(z\mid x)\ne\emptyset$ for all large $N$, and every sequence $z_N\in\arg\min_{z\in\mathcal Z}\widehat C_N(z\mid x)$ (for all large $N$) satisfies
--   $$\lim_{N\to\infty}\min_{z\in\mathcal Z}\widehat C_N(z\mid x)=v^*(x),\qquad \lim_{N\to\infty}C(z_N\mid x)=v^*(x),\qquad \lim_{N\to\infty}\ \inf_{z\in\mathcal Z^*(x)}\|z-z_N\|=0 .$$
--
--   This is the deterministic optimization step of the paper's argument: once the sample objective converges to the true conditional objective at $x$, the optimal values and the optimal decisions converge as well.
--
--   **Formalization Note** The paper states Lemma 6 under Assumption 5 in both cases, with the extra hypothesis $\hat\mu_{Y|x,N}\to\mu_{Y|x}$ weakly. As printed it is false in case 2 ($\mathcal Z$ unbounded): with $\mathcal Y=\mathcal Z=\mathbb R$, $\mu_{Y|x}=\delta_0$, $D_x=\{0\}$, $c(z;y)=\min(1+|z|,\,||z|-2/|y||)$ for $y\neq0$, $c(z;0)=1+|z|$ and $\hat\mu_{Y|x,N}=\delta_{1/N}$, every hypothesis holds but $\min_z\widehat C_N(z\mid x)=0$ while $v^*(x)=1$. The Lean therefore states case 1 only; the weak-convergence hypothesis is used only in case 2 and is dropped. $v^*(x)$ is read as $C(z^\star\mid x)$ for each $z^\star\in\mathcal Z^*(x)$, and $\min_{z}\widehat C_N(z\mid x)$ as $\widehat C_N(z_N\mid x)$ at a minimizer; the attainment of both minima is part of the conclusion. Integrability at $x$, $\mu_{Y|x}(\mathcal Y)=1$, $y^i\in\mathcal Y$ and the normalization of the weights are read as in Lemma 5. `Metric.infDist` is the distance to $\mathcal Z^*(x)$, which is nonempty by the first conclusion.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 45–47, Lemma 6 (case 1 of Assumption 5)

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- **Lemma 6, case 1 of Assumption 5 (`𝒵` bounded)** (arXiv:1402.5481v4, pp. 45–47). Fix `x` and one
sample path: weights `w N i` that are eventually nonnegative and sum to 1, observations `ys i ∈ 𝒴`.
Let `𝒵` be closed, bounded and nonempty, `c(z; ·)` integrable under `μ_{Y|x}` for every `z ∈ 𝒵`,
`c` equicontinuous in `z` on `𝒴` with `μ_{Y|x}(𝒴) = 1`, and `Ĉ_N(z|x) → C(z|x)` for every `z ∈ 𝒵`.
Then `𝒵*(x) ≠ ∅`, the argmin of `Ĉ_N(·|x)` over `𝒵` is eventually nonempty, and every sequence
`z_N` of eventual minimizers of `Ĉ_N(·|x)` over `𝒵` satisfies, for every `z⋆ ∈ 𝒵*(x)`,
`min_{z ∈ 𝒵} Ĉ_N(z|x) = Ĉ_N(z_N|x) → v*(x) = C(z⋆|x)` and `C(z_N|x) → v*(x)`, and
`inf_{z ∈ 𝒵*(x)} ‖z - z_N‖ → 0`. The printed hypothesis `μ̂_{Y|x,N} → μ_{Y|x}` weakly is used only in
case 2 and is dropped. -/
theorem lemma_6_bounded_case
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hZ_closed : IsClosed Z) (hZ_bdd : Bornology.IsBounded Z) (hZ_ne : Z.Nonempty)
    (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h3x : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x))
    (h4 : Assumption4 c Z Ys)
    (hconv : ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x))) :
    (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (weightedArgmin c w ys Z N).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz), (∀ᶠ N in atTop, zN N ∈ weightedArgmin c w ys Z N) →
        (∀ zstar ∈ optSet μ c Z x,
          Tendsto (fun N => weightedCost c w ys N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
          Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))) ∧
        Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0) := by sorry

end PrescAnalytics.KNN
