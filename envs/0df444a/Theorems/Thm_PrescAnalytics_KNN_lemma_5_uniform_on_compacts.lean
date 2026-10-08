-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_lemma_5_uniform_on_compacts
-- name    : PrescAnalytics.KNN.lemma_5_uniform_on_compacts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:54.00592+00:00
-- url     : https://prove2.me/theorems/00106b53-bc29-41bf-954b-4685a1f240d0
-- title:
--   Lemma 5 — pointwise convergence of Ĉ_N(·|x) is uniform on compact subsets of 𝒵
-- statement:
--   Fix a covariate value $x$ and one sample path of data: weights $w_{N,i}$ that are nonnegative and sum to $1$ for all large $N$, and observations $y^i\in\mathcal Y$. Suppose $c(z;\cdot)$ is integrable under $\mu_{Y|x}$ for every $z\in\mathcal Z$ (Assumption 3 at $x$), $c$ is equicontinuous in $z$ (Assumption 4), $\mu_{Y|x}(\mathcal Y)=1$, and for every $z\in\mathcal Z$,
--   $$\widehat C_N(z\mid x)=\sum_{i=1}^N w_{N,i}\,c(z;y^i)\ \longrightarrow\ C(z\mid x).$$
--   Then for every compact $K\subseteq\mathcal Z$,
--   $$\sup_{z\in K}\big|\widehat C_N(z\mid x)-C(z\mid x)\big|\ \longrightarrow\ 0 .$$
--
--   This upgrade from pointwise to locally uniform convergence is what lets Lemma 6 pass from convergence of the objectives to convergence of their minima and minimizers.
--
--   **Formalization Note** The paper's "Assumptions 3 and 4 hold" at the fixed $x$ is read as: $c(z;\cdot)$ is $\mu_{Y|x}$-integrable for every $z\in\mathcal Z$ (Assumption 3 gives this only for a.e. $x$, so it is a hypothesis at the fixed $x$), and Assumption 4 on $\mathcal Y$, together with $\mu_{Y|x}(\mathcal Y)=1$ and $y^i\in\mathcal Y$ for every $i$. The weights being eventually nonnegative and summing to $1$ is the reading of the paper's $\mathbb E_{\hat\mu_{Y|x,N}}$ notation. $\mu_{Y|x}$ is `μ.condKernel x`. Uniform convergence is Mathlib's `TendstoUniformlyOn`.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 45, Lemma 5

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- **Lemma 5** (arXiv:1402.5481v4, p. 45). Fix `x` and one sample path: weights `w N i` that are
eventually nonnegative and sum to 1, and observations `ys i ∈ 𝒴`. Suppose `c(z; ·)` is integrable
under `μ_{Y|x}` for every `z ∈ 𝒵` (Assumption 3 at `x`), `c` is equicontinuous in `z` on `𝒴`
(Assumption 4) with `μ_{Y|x}(𝒴) = 1`, and `Ĉ_N(z|x) → C(z|x)` for every `z ∈ 𝒵`. Then the
convergence is uniform in `z` over every compact subset of `𝒵`. -/
theorem lemma_5_uniform_on_compacts
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h3x : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x))
    (h4 : Assumption4 c Z Ys)
    (hconv : ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x)))
    (K : Set (EuclideanSpace ℝ (Fin dz))) (hK : IsCompact K) (hKZ : K ⊆ Z) :
    TendstoUniformlyOn (fun N z => weightedCost c w ys N z) (fun z => condCost μ c z x) atTop K := by sorry

end PrescAnalytics.KNN
