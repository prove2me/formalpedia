-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_height_of_simplex
-- name    : SmoothedSimplex.Shadow.height_of_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:17:58.946044+00:00
-- url     : https://prove2.me/theorems/20c45b3d-c681-48af-ac8b-aef6aec073c3
-- title:
--   Lemma 4.1.3 — height of simplex: $\Pr[\mathrm{dist}(b_1,\mathrm{Aff}(b_2,\dots,b_d))<\varepsilon]\le(3\varepsilon e^{2/3}d/\sigma^2)^3$
-- statement:
--   Let $n>d\ge3$ and let $\mu_1,\dots,\mu_d$ be Gaussian distributions in $\mathbb R^{d-1}$ of standard deviation $\sigma$ with $0<\sigma\le 1/(3\sqrt{d\ln n})$, centered at points of norm at most $3$. Let $(b_1,\dots,b_d)\in Q$ have density proportional to
--
--   $$
--   \mathrm{Vol}\big(\triangle(b_1,\dots,b_d)\big)\prod_{i=1}^{d}\mu_i(b_i).
--   $$
--
--   Then
--
--   $$
--   \Pr_{(b_1,\dots,b_d)\in Q}\big[\mathrm{dist}(b_1,\mathrm{Aff}(b_2,\dots,b_d))<\varepsilon\big]\le\Big(\frac{3\varepsilon e^{2/3}d}{\sigma^2}\Big)^{3}.
--   $$
--
--   The height of the random simplex over the face opposite $b_1$ is unlikely to be small; this is the input to Lemma 4.1.2.
--
--   **Formalization Note** The page's "$\mathrm{dist}(b_1,\mathrm{Aff}(b_2,\dots,b_d)<\varepsilon)$" is a misplaced parenthesis. $n$ enters only through the bound on $\sigma$; $d\ge3$ and $n>d$ are the standing assumptions of Section 4. The conditional probability is cross-multiplied: the $\mathrm{Vol}$-weighted Gaussian mass of $Q\cap\{\text{event}\}$ is at most the bound times that of $Q$. $\mathrm{Vol}$ is $(d-1)$-dimensional Lebesgue measure.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.1.3, printed pp. 49–50 (PDF pp. 49–50)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_setQ

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.1.3 (Height of simplex)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.1.3,
printed pp. 49–50, PDF pp. 49–50). Let `µ₁, …, µ_d` be Gaussian measures in `ℝ^{d−1}` of
standard deviation `σ ≤ 1/(3√(d ln n))` centered at points of norm at most 3. Then
`Pr_{b₁,…,b_d ∈ Q}[dist(b₁, Aff(b₂, …, b_d)) < ε] ≤ (3εe^{2/3}d/σ²)³`, where `b₁, …, b_d` have
density proportional to `Vol(△(b₁, …, b_d)) ∏ᵢ µᵢ(bᵢ)`.

**Formalization Note.**
* The page's typo `dist(b₁, Aff(b₂, …, b_d) < ε)` is read `dist(b₁, Aff(b₂, …, b_d)) < ε`.
* `n` enters only through `σ ≤ 1/(3√(d ln n))`; the hypotheses `d ≥ 3`, `n > d` are §4's standing
  assumptions (Theorem 4.0.1), added so that `ln n > 0`. `σ > 0`.
* "`Pr_{b∈Q}` with density proportional to `Vol(△(b)) ∏ µᵢ(bᵢ)`" is cross-multiplied:
  `∫_{Q ∩ event} Vol(△(b)) dµ(b) ≤ bound · ∫_Q Vol(△(b)) dµ(b)`, `µ = ∏ gaussian (cᵢ) σ`.
* `Vol(△(b))` is the `(d−1)`-dimensional Lebesgue measure of `convexHull {b₁, …, b_d}` in
  `ℝ^{d−1}`. Indices are 0-based (`b₁` is `b 0`). -/
theorem height_of_simplex {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn : d < n) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (c : Fin d → EuclideanSpace ℝ (Fin (d - 1))) (hc : ∀ i, ‖c i‖ ≤ 3) (ε : ℝ) :
    ∫⁻ b in setQ ∩ {b | Metric.infDist (b 0) (affineSpan ℝ (b '' {i | i ≠ 0}) : Set _) < ε},
        volume (convexHull ℝ (Set.range b)) ∂(Measure.pi fun i => gaussian (c i) σ) ≤
      ENNReal.ofReal ((3 * ε * Real.exp (2 / 3) * d / σ ^ 2) ^ 3) *
        ∫⁻ b in setQ, volume (convexHull ℝ (Set.range b)) ∂(Measure.pi fun i => gaussian (c i) σ) := by sorry

end SmoothedSimplex.Shadow
