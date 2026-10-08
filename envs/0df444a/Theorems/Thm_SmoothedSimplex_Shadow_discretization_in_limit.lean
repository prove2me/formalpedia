-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_discretization_in_limit
-- name    : SmoothedSimplex.Shadow.discretization_in_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:18:13.002385+00:00
-- url     : https://prove2.me/theorems/47ee1fb8-eb1d-4711-92e8-f8574aab4e6b
-- title:
--   Lemma 4.0.6 — discretization in limit
-- statement:
--   Let $z$ and $t$ be nonzero orthogonal vectors in $\mathbb R^d$, and let $a_1,\dots,a_n$ be independent random vectors with non-degenerate Gaussian distributions $\mu_1,\dots,\mu_n$ (arbitrary centers, positive definite covariances). For $\theta\in\mathbb R$ put $q_\theta=z\sin\theta+t\cos\theta$. Then
--
--   $$
--   \mathbb E\Big[\Big|\bigcup_{q\in\mathrm{Span}(z,t)}\{\mathrm{optSimp}_q(a_1,\dots,a_n)\}\Big|\Big]
--   =\lim_{m\to\infty}\mathbb E\Big[\Big|\bigcup_{\theta\in\{2\pi/m,\,2\cdot2\pi/m,\,\dots,\,m\cdot2\pi/m\}}\{\mathrm{optSimp}_{q_\theta}(a_1,\dots,a_n)\}\Big|\Big],
--   $$
--
--   and all the sizes involved are measurable.
--
--   The lemma reduces the continuous shadow to a count over $m$ equally spaced directions, which can then be bounded by a union bound over the $m$ angular steps.
--
--   **Formalization Note** The left-hand union is the shadow $\mathrm{Shadow}_{t,z}(a)$, a set of index sets (directions $q\neq0$). Expectations are lower Lebesgue integrals of the sizes, and their a.e.-measurability is part of the conclusion. A non-degenerate Gaussian is Mathlib's `multivariateGaussian` with a positive definite covariance matrix. The lemma says "orthogonal vectors"; they are taken nonzero, as in its application to the independent $z,t$ of Theorem 4.0.1.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.0.6, printed p. 40 (PDF p. 40); q_θ from eq. (11), p. 39

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_optSimp
import Definitions.Def_SmoothedSimplex_Shadow_shadow

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open Filter Topology

open Classical in
/-- **Lemma 4.0.6 (Discretization in limit)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.0.6,
printed p. 40, PDF p. 40; eq. (11), p. 39). Let `z` and `t` be orthogonal vectors in `ℝ^d`, and
let `µ₁, …, µₙ` be non-degenerate Gaussian distributions. Then
`E[|⋃_{q∈Span(z,t)} {optSimp_q(a)}|] = lim_{m→∞} E[|⋃_{θ∈{2π/m, 2·2π/m, …, m·2π/m}} {optSimp_{q_θ}(a)}|]`,
where `q_θ = z sin θ + t cos θ`.

**Formalization Note.**
* `z, t` are nonzero (the lemma is applied to the independent `z, t` of Theorem 4.0.1; with
  `t = 0` the grid would contain `q = 0`).
* A non-degenerate Gaussian is `multivariateGaussian (ā i) (S i)` with `S i` positive definite;
  the `aᵢ` are independent (product measure), as in Theorem 4.0.1.
* Both unions are read as in `shadow`: sets of index sets `I` (the left-hand side is
  `shadow t z a`); the grid is `θ = 2πk/m`, `k = 1, …, m`.
* Expectations are lower Lebesgue integrals of the `ℝ≥0∞`-valued sizes; a.e.-measurability of
  every size is part of the conclusion. -/
theorem discretization_in_limit {d n : ℕ} (z t : EuclideanSpace ℝ (Fin d)) (hz : z ≠ 0)
    (ht : t ≠ 0) (hzt : ⟪z, t⟫ = 0) (abar : Fin n → EuclideanSpace ℝ (Fin d))
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosDef) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) :=
      Measure.pi (fun i => multivariateGaussian (abar i) (S i))
    let grid : ℕ → (Fin n → EuclideanSpace ℝ (Fin d)) → Finset (Finset (Fin n)) := fun m a =>
      Finset.univ.filter (fun I => ∃ k ∈ Finset.Icc 1 m,
        I ∈ optSimp (Real.sin (2 * Real.pi * k / m) • z + Real.cos (2 * Real.pi * k / m) • t) a)
    AEMeasurable (fun a => ((shadow t z a).card : ENNReal)) μ ∧
    (∀ m, AEMeasurable (fun a => ((grid m a).card : ENNReal)) μ) ∧
    Tendsto (fun m : ℕ => ∫⁻ a, ((grid m a).card : ENNReal) ∂μ) atTop
      (𝓝 (∫⁻ a, ((shadow t z a).card : ENNReal) ∂μ)) := by sorry

end SmoothedSimplex.Shadow
