-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_shadow_size_bound
-- name    : SmoothedSimplex.Shadow.shadow_size_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:18:30.233192+00:00
-- url     : https://prove2.me/theorems/e0c475e1-7c9d-4bd3-b78a-eff5272fa4bf
-- title:
--   Theorem 4.0.1 (Shadow Size) — $\mathbb E|\mathrm{Shadow}_{t,z}(a_1,\dots,a_n)|\le\mathcal D(n,d,\sigma)$
-- statement:
--   Let $d\ge3$ and $n>d$. Let $z$ and $t$ be linearly independent vectors in $\mathbb R^d$, and let $a_1,\dots,a_n$ be independent random vectors, $a_i$ Gaussian of standard deviation $\sigma>0$ centered at a point $\bar a_i$ with $\|\bar a_i\|\le1$ (joint density $\prod_{i=1}^n\mu_i(a_i)$). Then
--
--   $$
--   \mathbb E_{a_1,\dots,a_n}\big[\,|\mathrm{Shadow}_{t,z}(a_1,\dots,a_n)|\,\big]\le\mathcal D(n,d,\sigma)=\frac{58{,}888{,}678\,nd^3}{\min\big(\sigma,1/(3\sqrt{d\ln n})\big)^6}. \tag{10}
--   $$
--
--   The shadow of the polyhedron $\{x:\langle a_i|x\rangle\le1\}$ on a fixed two-dimensional plane is the polygon along which the shadow-vertex simplex method walks, so its expected number of vertices bounds the expected number of pivots. The theorem shows that this number is polynomial in $n$, $d$ and $1/\sigma$ for every choice of the centers, which is the geometric core of the polynomial smoothed complexity of the simplex method.
--
--   **Formalization Note** $|\mathrm{Shadow}_{t,z}|$ is the number of index sets $I$ that belong to $\mathrm{optSimp}_q(a)$ for some nonzero $q\in\mathrm{Span}(t,z)$. The expectation is the lower Lebesgue integral of this size, and its a.e.-measurability is part of the conclusion.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time, arXiv:cs/0111050v7, Theorem 4.0.1, eq. (10), printed p. 38 (PDF p. 38)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_shadow
import Definitions.Def_SmoothedSimplex_Shadow_shadowBound

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Theorem 4.0.1 (Shadow Size)** (Spielman & Teng, *Smoothed Analysis of Algorithms: Why the
Simplex Algorithm Usually Takes Polynomial Time*, arXiv:cs/0111050v7, Theorem 4.0.1, printed p. 38,
PDF p. 38). Let `d ≥ 3` and `n > d`. Let `z` and `t` be independent vectors in `ℝ^d`, and let
`µ₁, …, µₙ` be Gaussian distributions in `ℝ^d` of standard deviation `σ` centered at points each of
norm at most 1. Then `E_{a₁,…,aₙ}[|Shadow_{t,z}(a₁, …, aₙ)|] ≤ 𝒟(n, d, σ)` (10), where
`𝒟(n, d, σ) = 58,888,678 nd³ / min(σ, 1/(3√(d ln n)))⁶`, and `a₁, …, aₙ` have density
`∏ᵢ µᵢ(aᵢ)`.

**Formalization Note.**
* "Independent vectors" is linear independence of `(z, t)`. `σ > 0`.
* The joint law is `Measure.pi (fun i => gaussian (ā i) σ)` (independent `aᵢ`).
* `|Shadow_{t,z}(a)|` is `(shadow t z a).card`, the number of index sets `I` with
  `I ∈ optSimp_q(a)` for some nonzero `q ∈ Span(t, z)` (see `shadow`).
* The expectation is the lower Lebesgue integral of the `ℝ≥0∞`-valued size, and the conclusion
  also asserts that the size is a.e.-measurable, so the integral is the expectation. -/
theorem shadow_size_bound {d n : ℕ} (hd : 3 ≤ d) (hn : d < n)
    (z t : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (σ : ℝ) (hσ : 0 < σ)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi (fun i => gaussian (abar i) σ)
    AEMeasurable (fun a => ((shadow t z a).card : ENNReal)) μ ∧
      ∫⁻ a, ((shadow t z a).card : ENNReal) ∂μ ≤ ENNReal.ofReal (shadowBound n d σ) := by sorry

end SmoothedSimplex.Shadow
