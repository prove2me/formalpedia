-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_distance_bound
-- name    : SmoothedSimplex.Shadow.distance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:35:00.564643+00:00
-- url     : https://prove2.me/theorems/027c89c7-1b91-44c0-835e-81d9d6e6358b
-- title:
--   Lemma 4.1.1 — distance bound (17)
-- statement:
--   Let $n>d\ge3$, let $q\in\mathbb R^d$ be a unit vector, and let $\mu_1,\dots,\mu_n$ be Gaussian distributions in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points $\bar a_i$ of norm at most $1$. Identify $\mathbb R^{d-1}$ with $q^\perp$ by any linear isometry, and let $R_\omega$ be the rotation taking $q$ to $\omega$. Consider variables $\omega\in S^{d-1}$, $s\in(0,2]$ and $(b_1,\dots,b_d)\in Q$ with density proportional to
--
--   $$
--   \langle\omega|q\rangle\,\mathrm{Vol}\big(\triangle(b_1,\dots,b_d)\big)\Big(\prod_{j>d}\int_{a_j}\big[\langle\omega|a_j\rangle\le s\langle\omega|q\rangle\big]\mu_j(a_j)\,da_j\Big)\prod_{i=1}^{d}\mu_i(R_\omega b_i+sq).
--   $$
--
--   Then
--
--   $$
--   \Pr_{\omega,\ s\le2,\ (b_1,\dots,b_d)\in Q}\big[\mathrm{dist}(0,\mathrm{Aff}(b_2,\dots,b_d))<\varepsilon\big]\le\frac{900\,e^{2/3}d^2\varepsilon}{\sigma^4}. \tag{17}
--   $$
--
--   This is the distance half of the bound on the angle $\mathrm{ang}(q,\triangle(a_2,\dots,a_d))$ in Lemma 4.0.11, expressed in the coordinates of the Blaschke change of variables (Corollary 2.5.3).
--
--   **Formalization Note** $\omega$ ranges over the unit sphere with its surface measure (Mathlib's `volume.toSphere`, a constant multiple of surface area); the factor $\langle\omega|q\rangle$ enters through its positive part, so only the hemisphere $\langle\omega|q\rangle>0$ carries mass. $s$ ranges over $(0,2]$ and $(b_1,\dots,b_d)$ over $Q\subseteq(\mathbb R^{d-1})^d$, both with Lebesgue measure. The statement holds for every identification of $\mathbb R^{d-1}$ with $q^\perp$, which the paper calls arbitrary. The probability is cross-multiplied, as iterated integrals over $\omega$, $s$ and $b$. $d\ge3$, $n>d$ are the standing assumptions of Section 4.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.1.1, eq. (17), printed p. 45 (PDF p. 45)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_setQ
import Definitions.Def_SmoothedSimplex_Shadow_underPlaneMass
import Definitions.Def_SmoothedSimplex_Shadow_planeDensity

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.1.1 (Distance bound)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.1.1,
printed p. 45, PDF p. 45). Let `q` be a unit vector and let `µ₁, …, µₙ` be Gaussian measures in
`ℝ^d` of standard deviation `σ ≤ 1/(3√(d ln n))` centered at points of norm at most 1. Then
`Pr_{ω, s≤2, (b₁,…,b_d)∈Q}[dist(0, Aff(b₂, …, b_d)) < ε] ≤ 900e^{2/3}d²ε/σ⁴` (17), where the
variables have density proportional to
`⟨ω|q⟩ Vol(△(b₁, …, b_d)) (∏_{j>d} ∫ [⟨ω|aⱼ⟩ ≤ s⟨ω|q⟩] µⱼ(aⱼ) daⱼ) ∏_{i=1}^d µᵢ(R_ω bᵢ + sq)`.

**Formalization Note.**
* Domains (readings of the page, from the change of variables of Corollary 2.5.3):
  `ω` ranges over the unit sphere `S^{d−1}` with its surface measure (Mathlib's
  `volume.toSphere`, a constant multiple of surface area — the constant cancels); the factor
  `⟨ω|q⟩` enters as `max(⟨ω|q⟩, 0)`, so only the hemisphere `⟨ω|q⟩ > 0` carries mass;
  `s ∈ (0, 2]` with Lebesgue measure; `(b₁, …, b_d) ∈ Q ⊂ (ℝ^{d−1})^d` with Lebesgue measure.
* `bᵢ ∈ ℝ^{d−1}` is identified with `q^⊥` by an arbitrary linear isometry `φ` (the paper's
  "arbitrary coordinatization", p. 25); the statement holds for every `φ`. `R_ω` is `rotTo q ω`.
* The probability is cross-multiplied: (mass of the event) `≤ bound ·` (total mass), as iterated
  lower Lebesgue integrals over `ω`, `s`, `b`.
* `d ≥ 3`, `n > d` are §4's standing assumptions (Theorem 4.0.1), added so that `ln n > 0`;
  `σ > 0`. Indices are 0-based. -/
theorem distance_bound {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn : d < n)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1)
    (φ : EuclideanSpace ℝ (Fin (d - 1)) ≃ₗᵢ[ℝ] (Submodule.span ℝ {q})ᗮ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (ε : ℝ) :
    let ν : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ →
        (Fin d → EuclideanSpace ℝ (Fin (d - 1))) → ENNReal := fun ω s b =>
      ENNReal.ofReal ⟪(ω : EuclideanSpace ℝ (Fin d)), q⟫ * volume (convexHull ℝ (Set.range b)) *
        underPlaneMass abar σ ω q s * planeDensity q φ abar σ ω s b
    ∫⁻ ω, ∫⁻ s in Set.Ioc 0 2,
        ∫⁻ b in setQ ∩ {b | Metric.infDist (0 : EuclideanSpace ℝ (Fin (d - 1))) (affineSpan ℝ (b '' {i | i ≠ 0}) : Set _) < ε},
          ν ω s b ∂volume ∂volume ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere ≤
      ENNReal.ofReal (900 * Real.exp (2 / 3) * d ^ 2 * ε / σ ^ 4) *
        ∫⁻ ω, ∫⁻ s in Set.Ioc 0 2, ∫⁻ b in setQ,
          ν ω s b ∂volume ∂volume ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by sorry

end SmoothedSimplex.Shadow
