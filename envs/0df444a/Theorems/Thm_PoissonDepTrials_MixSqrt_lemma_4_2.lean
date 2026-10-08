-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_2
-- name    : PoissonDepTrials.MixSqrt.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:59.765887+00:00
-- url     : https://prove2.me/theorems/ca5d48b2-b923-4e66-93d3-67d49ab583de
-- title:
--   Lemma 4.2, p. 539 — |E^Y f(Y, Z) − E^Y f(Y, Z′)| ≤ 2‖f‖φ(m) a.s. for Y ∈ ℳ_{1k}, Z ∈ ℳ_{k+m,∞}
-- statement:
--   Let $X_1,X_2,\dots$ be an arbitrary sequence of real random variables satisfying Ibragimov's mixing condition (4.1) with $\varphi$, and let $m\ge1$. Let $Y=(Y_1,\dots,Y_r)$ be an $\mathcal M_{1k}$-measurable and $Z=(Z_1,\dots,Z_s)$ an $\mathcal M_{k+m,\infty}$-measurable random vector, and let $f:\mathbb R^{r}\times\mathbb R^{s}\to\mathbb R$ be Borel with $|f|\le M$. Then, almost surely,
--   $$\Bigl|E^Yf(Y,Z)-\int f(Y,z)\,\hat P(dz)\Bigr|\le 2M\varphi(m),$$
--   where $\hat P$ is the law of $Z$. The integral is $E^Yf(Y,Z')$ for a copy $Z'$ of $Z$ independent of the sequence, so this is the paper's (4.4), $|E^Yf(Y,Z)-E^Yf(Y,Z')|\le2\|f\|\varphi(m)$.
--
--   The lemma measures how far conditioning on the past moves the law of a well-separated future; Lemma 4.3 is derived from it.
--
--   **Formalization Note** $\mathbb R^{r+s}$ is written as the product $\mathbb R^r\times\mathbb R^s$. The independent copy $Z'$ is not built on an enlarged space: $E^Yf(Y,Z')$ is written as $\int f(Y,z)\,d\hat P(z)$, its value. $E^Y$ is the conditional expectation given $\sigma(Y)$. $m\ge1$ because (4.1) is stated for lags $k\ge1$; every $X_i$ is measurable.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 539, Lemma 4.2, (4.4)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.2, p. 539, (4.4). Let `X_1, X_2, …` be a real sequence satisfying (4.1),
`Y` an `ℳ_{1k}`-measurable `ℝ^r`-valued and `Z` an `ℳ_{k+m,∞}`-measurable `ℝ^s`-valued random
vector, and `f` bounded by `M` and Borel. Then almost surely
`|E^Y f(Y, Z) − E^Y f(Y, Z')| ≤ 2‖f‖φ(m)`, where `E^Y f(Y, Z') = ∫ f(Y, z) dP_Z(z)` for an independent
copy `Z'` of `Z`. -/
theorem lemma_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m := by sorry

end PoissonDepTrials.MixSqrt
