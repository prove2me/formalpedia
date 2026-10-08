-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_chi_square_bound
-- name    : SmoothedSimplex.Shadow.chi_square_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:17:40.551121+00:00
-- url     : https://prove2.me/theorems/409f91d0-9393-4701-bd00-77e9899fb8c0
-- title:
--   Corollary 2.4.6 — a chi-square bound: $\Pr[\|x\|\ge 3\sqrt{d\ln n}\,\sigma]\le n^{-2.9d}$
-- statement:
--   Let $x$ be a Gaussian random vector in $\mathbb R^d$ of standard deviation $\sigma>0$ centered at the origin. Then, for every integer $n\ge 3$,
--
--   $$
--   \Pr\big[\|x\|\ge 3\sqrt{d\ln n}\,\sigma\big]\le n^{-2.9d}.
--   $$
--
--   Moreover, if $n>d\ge3$ and $x_1,\dots,x_n$ are such vectors, then
--
--   $$
--   \Pr\Big[\max_i\|x_i\|\ge 3\sqrt{d\ln n}\,\sigma\Big]\le n^{-2.9d+1}\le 0.0015\binom{n}{d}^{-1}.
--   $$
--
--   The corollary says that a perturbation of standard deviation $\sigma\le 1/(3\sqrt{d\ln n})$ moves no data point by more than $1$, except with probability small enough to absorb the trivial bound $\binom nd$ on the shadow size.
--
--   **Formalization Note** In the second part the vectors live on an arbitrary probability space, each with the Gaussian law; no independence is assumed (the bound is a union bound). $\max_i\|x_i\|\ge r$ is written "some $\|x_i\|\ge r$".
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Corollary 2.4.6, printed p. 21 (PDF p. 21)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Corollary 2.4.6 (A chi-square bound)** (Spielman & Teng, *Smoothed Analysis of Algorithms*,
arXiv:cs/0111050v7, Corollary 2.4.6, printed p. 21, PDF p. 21). Let `x` be a Gaussian random
vector in `ℝ^d` of standard deviation `σ` centered at the origin. Then, for `n ≥ 3`,
`Pr[‖x‖ ≥ 3√(d ln n) σ] ≤ n^{−2.9d}`. Moreover, if `n > d ≥ 3` and `x₁, …, xₙ` are such
vectors, then `Pr[maxᵢ ‖xᵢ‖ ≥ 3√(d ln n) σ] ≤ n^{−2.9d+1} ≤ 0.0015 · C(n, d)^{−1}`.

**Formalization Note.** `σ > 0`. The vectors `x₁, …, xₙ` of the second part live on an
arbitrary probability space, each with law `gaussian 0 σ`; no independence is assumed (the page
assumes none; the bound is a union bound). `maxᵢ ‖xᵢ‖ ≥ r` is written `∃ i, ‖xᵢ‖ ≥ r`.
`n^{−2.9d}` is the real power `(n : ℝ) ^ (−(29/10) d)`, and `ln` is `Real.log` (positive for
`n ≥ 3`). -/
theorem chi_square_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (σ : ℝ) (hσ : 0 < σ) :
    (∀ n : ℕ, 3 ≤ n →
      gaussian (0 : EuclideanSpace ℝ (Fin d)) σ
          {x | 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖x‖}
        ≤ ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d))) ∧
    (∀ n : ℕ, d < n → 3 ≤ d →
      ∀ (P : Measure Ω) [IsProbabilityMeasure P] (x : Fin n → Ω → EuclideanSpace ℝ (Fin d)),
        (∀ i, AEMeasurable (x i) P) → (∀ i, P.map (x i) = gaussian 0 σ) →
        P {ω | ∃ i, 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖x i ω‖}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) ∧
          (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) ≤ (15 / 10000 : ℝ) * ((n.choose d : ℕ) : ℝ)⁻¹) := by sorry

end SmoothedSimplex.Shadow
