-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_angle_of_incidence
-- name    : SmoothedSimplex.Shadow.angle_of_incidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:35:11.251916+00:00
-- url     : https://prove2.me/theorems/ee407b63-7d0f-4740-be86-30ab4c53a052
-- title:
--   Lemma 4.2.1 — angle of incidence: $\Pr_\omega[\langle\omega|q\rangle<\varepsilon]<(340\varepsilon n/\sigma^2)^2$
-- statement:
--   Let $d\ge3$ and $n>d$. Let $\mu_1,\dots,\mu_n$ be Gaussian densities in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points of norm at most $1$. Let $q$ be the reference unit vector, identify $\mathbb R^{d-1}$ with $q^\perp$ by a linear isometry, let $0\le s\le2$ and let $(b_1,\dots,b_d)\in Q$. Let $\omega\in S^{d-1}$ have density proportional to
--
--   $$
--   \langle\omega|q\rangle\Big(\prod_{j>d}\int_{a_j}\big[\langle\omega|a_j\rangle\le s\langle\omega|q\rangle\big]\mu_j(a_j)\,da_j\Big)\prod_{i=1}^d\mu_i(R_\omega b_i+sq).
--   $$
--
--   Then for every $\varepsilon>0$
--
--   $$
--   \Pr_\omega\big[\langle\omega|q\rangle<\varepsilon\big]<\Big(\frac{340\,\varepsilon n}{\sigma^2}\Big)^2. \tag{25}
--   $$
--
--   The normal $\omega$ of the facet hit by the ray through $q$ is unlikely to be nearly orthogonal to $q$; this is the angle half of the bound in Lemma 4.0.11.
--
--   **Formalization Note** $\omega$ ranges over the unit sphere with Mathlib's `volume.toSphere` (a constant multiple of surface measure); the factor $\langle\omega|q\rangle$ enters through its positive part. Added hypotheses: $\sigma\le1/(3\sqrt{d\ln n})$ (the standing assumption of Section 4; the proof passes through Lemma 4.2.2, which needs it), $s\ge0$ and $\varepsilon>0$. The statement holds for every identification of $\mathbb R^{d-1}$ with $q^\perp$. The probability is cross-multiplied.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.2.1, eq. (25), printed p. 52 (PDF p. 52)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_setQ
import Definitions.Def_SmoothedSimplex_Shadow_underPlaneMass
import Definitions.Def_SmoothedSimplex_Shadow_planeDensity

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.2.1 (Angle of incidence)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.2.1,
printed p. 52, PDF p. 52). Let `d ≥ 3` and `n > d`. Let `µ₁, …, µₙ` be Gaussian densities in `ℝ^d`
of standard deviation `σ` centered at points of norm at most 1. Let `s ≤ 2` and let
`(b₁, …, b_d) ∈ Q`. Then `Pr_ω[⟨ω|q⟩ < ε] < (340εn/σ²)²` (25), where `ω` has density
proportional to `⟨ω|q⟩ (∏_{j>d} ∫ [⟨ω|aⱼ⟩ ≤ s⟨ω|q⟩] µⱼ(aⱼ) daⱼ) ∏_{i=1}^d µᵢ(R_ω bᵢ + sq)`.

**Formalization Note.**
* `ω` ranges over the unit sphere `S^{d−1}` with Mathlib's `volume.toSphere` (a constant multiple
  of surface measure); the factor `⟨ω|q⟩` enters as `max(⟨ω|q⟩, 0)`, so only the hemisphere
  `⟨ω|q⟩ > 0` carries mass. `q` is the reference unit vector of §2.5; `bᵢ ∈ ℝ^{d−1}` is placed in
  `q^⊥` by an arbitrary linear isometry `φ` (every `φ`); `R_ω` is `rotTo q ω`.
* **Added hypotheses**: `σ ≤ 1/(3√(d ln n))` (§4's standing assumption; the proof goes through
  Lemma 4.2.2, which is false without a bound on `σ`), `0 ≤ s` (Lemma 4.2.3 requires `s ≥ 0`; in the
  application `s > 0`), and `0 < ε` (at `ε = 0` the strict inequality fails).
* Cross-multiplied: (mass of `{⟨ω|q⟩ < ε}`) `<` bound `·` (total mass), lower Lebesgue integrals. -/
theorem angle_of_incidence {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn : d < n)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1)
    (φ : EuclideanSpace ℝ (Fin (d - 1)) ≃ₗᵢ[ℝ] (Submodule.span ℝ {q})ᗮ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (b : Fin d → EuclideanSpace ℝ (Fin (d - 1))) (hb : b ∈ setQ) (ε : ℝ) (hε : 0 < ε) :
    let ν : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ENNReal := fun ω =>
      ENNReal.ofReal ⟪(ω : EuclideanSpace ℝ (Fin d)), q⟫ * underPlaneMass abar σ ω q s *
        planeDensity q φ abar σ ω s b
    ∫⁻ ω in {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 |
          ⟪(ω : EuclideanSpace ℝ (Fin d)), q⟫ < ε},
        ν ω ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere <
      ENNReal.ofReal ((340 * ε * n / σ ^ 2) ^ 2) *
        ∫⁻ ω, ν ω ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by sorry

end SmoothedSimplex.Shadow
