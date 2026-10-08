-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_distance_bound_in_plane
-- name    : SmoothedSimplex.Shadow.distance_bound_in_plane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:18:09.764046+00:00
-- url     : https://prove2.me/theorems/025326e6-d380-4cef-b287-555ff5dae683
-- title:
--   Lemma 4.1.2 — distance bound in plane: $\Pr[\mathrm{dist}(0,\mathrm{Aff}(b_2,\dots,b_d))<\varepsilon]\le 900e^{2/3}d^2\varepsilon/\sigma^4$
-- statement:
--   Let $n>d\ge3$ and let $\mu_1,\dots,\mu_d$ be Gaussian distributions in $\mathbb R^{d-1}$ of standard deviation $\sigma$ with $0<\sigma\le 1/(3\sqrt{d\ln n})$, centered at points of norm at most $3$. Let $(b_1,\dots,b_d)\in Q$ have density proportional to $\mathrm{Vol}(\triangle(b_1,\dots,b_d))\prod_{i=1}^d\mu_i(b_i)$. Then
--
--   $$
--   \Pr_{(b_1,\dots,b_d)\in Q}\big[\mathrm{dist}(0,\mathrm{Aff}(b_2,\dots,b_d))<\varepsilon\big]\le\frac{900\,e^{2/3}d^{2}\varepsilon}{\sigma^{4}}. \tag{18}
--   $$
--
--   The origin (the point where the ray through $q$ meets the facet) is unlikely to be close to the boundary face opposite $b_1$.
--
--   **Formalization Note** $n$ enters only through the bound on $\sigma$; $d\ge3$, $n>d$ are the standing assumptions of Section 4. The conditional probability is cross-multiplied as in Lemma 4.1.3.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.1.2, eq. (18), printed p. 46 (PDF p. 46)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_setQ

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.1.2 (Distance bound in plane)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.1.2,
printed p. 46, PDF p. 46). Let `µ₁, …, µ_d` be Gaussian measures in `ℝ^{d−1}` of standard
deviation `σ ≤ 1/(3√(d ln n))` centered at points of norm at most 3. Then
`Pr_{b₁,…,b_d ∈ Q}[dist(0, Aff(b₂, …, b_d)) < ε] ≤ 900e^{2/3}d²ε/σ⁴` (18), where `b₁, …, b_d`
have density proportional to `Vol(△(b₁, …, b_d)) ∏ᵢ µᵢ(bᵢ)`.

**Formalization Note.**
* `n` enters only through `σ ≤ 1/(3√(d ln n))`; `d ≥ 3`, `n > d` are §4's standing assumptions,
  added so that `ln n > 0`. `σ > 0`.
* Cross-multiplied: `∫_{Q ∩ event} Vol(△(b)) dµ(b) ≤ bound · ∫_Q Vol(△(b)) dµ(b)`, with
  `µ = ∏ gaussian (cᵢ) σ` and `Vol` the Lebesgue measure of `convexHull {b₁, …, b_d}` in `ℝ^{d−1}`.
* Indices are 0-based (`b₁` is `b 0`). -/
theorem distance_bound_in_plane {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn : d < n) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (c : Fin d → EuclideanSpace ℝ (Fin (d - 1))) (hc : ∀ i, ‖c i‖ ≤ 3) (ε : ℝ) :
    ∫⁻ b in setQ ∩ {b | Metric.infDist (0 : EuclideanSpace ℝ (Fin (d - 1))) (affineSpan ℝ (b '' {i | i ≠ 0}) : Set _) < ε},
        volume (convexHull ℝ (Set.range b)) ∂(Measure.pi fun i => gaussian (c i) σ) ≤
      ENNReal.ofReal (900 * Real.exp (2 / 3) * d ^ 2 * ε / σ ^ 4) *
        ∫⁻ b in setQ, volume (convexHull ℝ (Set.range b)) ∂(Measure.pi fun i => gaussian (c i) σ) := by sorry

end SmoothedSimplex.Shadow
