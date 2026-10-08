-- Prove2me | Theorems.Thm_UniformDRO_Concentration_lemma_9
-- name    : UniformDRO.Concentration.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:28.749989+00:00
-- url     : https://prove2.me/theorems/3068fb64-a7ba-4f0d-9567-9510894290e6
-- title:
--   Lemma 9, p. 39 — for Z ∈ [0, M], inf over η ∈ ℝ of g(η; P) equals the inf over η ∈ [−M/(c_k−1), M]
-- statement:
--   Let $P$ be a probability measure on $(\mathcal X,\mathcal A)$, $k>1$, $\rho>0$, $k_*=k/(k-1)$, $c_k=(1+k(k-1)\rho)^{1/k}$, and let $Z:\mathcal X\to[0,M]$ be measurable. With $g(\eta;P)=c_k\,\mathbb E_P[(Z-\eta)_+^{k_*}]^{1/k_*}+\eta$,
--   $$
--   \inf_{\eta\in\mathbb R}g(\eta;P)=\inf\Big\{g(\eta;P):\eta\in\Big[-\frac{1}{c_k-1}M,\,M\Big]\Big\}.
--   $$
--
--   Restricting the dual variable to a compact interval is what makes a finite grid of $\eta$ values, and hence a union bound, sufficient in the proof of Theorem 2.
--
--   **Formalization Note** Since $k>1$ and $\rho>0$ give $c_k>1$, the interval is nonempty ($-M/(c_k-1)\le0\le M$), and $g(\cdot;P)\ge\mathbb E_P[Z]\ge0$, so both infima are real infima of sets bounded below. Measurability of $Z$ is added. No condition $M\ge1$ is imposed: Lemma 9 holds for any $M\ge0$ (and $Z\in[0,M]$ forces $M\ge0$).
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 9, App. C.1, p. 39; proof pp. 39–40

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Lemma 9 (Duchi & Namkoong, arXiv:1810.08750v6, App. C.1, p. 39): if `Z ∈ [0, M]`, then for any
probability measure `P`,
`inf_{η ∈ ℝ} g_k(η; P) = inf { g_k(η; P) : η ∈ [-M/(c_k - 1), M] }`.
Both infima are of functions bounded below (`g_k(η; P) ≥ E_P[Z] ≥ 0`), and the interval is
nonempty because `c_k > 1`, so `-M/(c_k - 1) ≤ 0 ≤ M`. -/
theorem lemma_9 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (Z : X → ℝ) (hZm : Measurable Z) (M : ℝ)
    (hZ : ∀ x, Z x ∈ Set.Icc 0 M) :
    ⨅ η : ℝ, dualObjective k ρ P Z η =
      ⨅ η : Set.Icc (-(M / (ck k ρ - 1))) M, dualObjective k ρ P Z η := by sorry

end UniformDRO.Concentration
