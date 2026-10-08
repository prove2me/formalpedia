-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_angle_of_incidence_two
-- name    : SmoothedSimplex.Shadow.angle_of_incidence_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:35:03.752654+00:00
-- url     : https://prove2.me/theorems/d701293f-45e7-4518-aecd-21e5d9480ab0
-- title:
--   Lemma 4.2.2 — angle of incidence, II: $\Pr[c<\varepsilon]<(340\varepsilon n/\sigma^2)^2$
-- statement:
--   Let $d\ge3$ and $n>d$. Let $\mu_1,\dots,\mu_n$ be Gaussian densities in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points of norm at most $1$. Let $q$ be the reference unit vector, identify $\mathbb R^{d-1}$ with $q^\perp$ by a linear isometry, let $0\le s\le2$, let $b_1,\dots,b_d\in\mathbb R^{d-1}$ each have norm at most $4\sqrt2$, and let $\psi\in S^{d-2}$. For $c\in(0,1]$ let $\omega_{\psi,c}=(c,\psi\sqrt{1-c^2})$ in a coordinate system with first coordinate $q$. Let $c\in(0,1]$ have density proportional to
--
--   $$
--   (1-c^2)^{(d-3)/2}\cdot c\cdot\Big(\prod_{j>d}\int_{a_j}\big[\langle\omega_{\psi,c}|a_j\rangle\le s\langle\omega_{\psi,c}|q\rangle\big]\mu_j(a_j)\,da_j\Big)\prod_{i=1}^d\mu_i\big(R_{\omega_{\psi,c}}b_i+sq\big). \tag{26}
--   $$
--
--   Then for every $\varepsilon>0$
--
--   $$
--   \Pr[c<\varepsilon]<\Big(\frac{340\,\varepsilon n}{\sigma^2}\Big)^2 .
--   $$
--
--   This is Lemma 4.2.1 after the latitude–longitude change of variables of Proposition 2.5.4.
--
--   **Formalization Note** Added hypotheses, each recorded: $\sigma\le1/(3\sqrt{d\ln n})$ (the standing assumption of Section 4; for large $\sigma$ the bound tends to $0$ while $\Pr[c<\varepsilon]$ does not); $s\ge0$ (the proof applies Lemma 4.2.3, which requires it); $\varepsilon>0$ (at $\varepsilon=0$ both sides vanish). The page constrains only $\mu_{d+1},\dots,\mu_n$, but the density also involves $\mu_1,\dots,\mu_d$, which the proof treats as Gaussians of standard deviation $\sigma$ centered at points of norm at most $1$ (as in Lemma 4.2.1); all $n$ are constrained here. $\omega_{\psi,c}=c\,q+\sqrt{1-c^2}\,\varphi(\psi)$ for the chosen isometry $\varphi$, and the statement holds for every $\varphi$. The probability is cross-multiplied, with lower Lebesgue integrals over $(0,1]$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.2.2, eq. (26), printed pp. 52–53 (PDF pp. 52–53); ω_{ψ,c} from §2.5, p. 26

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_underPlaneMass
import Definitions.Def_SmoothedSimplex_Shadow_planeDensity

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.2.2 (Angle of incidence, II)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.2.2,
printed pp. 52–53, PDF pp. 52–53; `ω_{ψ,c}` from §2.5, p. 26). Let `d ≥ 3` and `n > d`. Let
`µ_{d+1}, …, µₙ` be Gaussian densities in `ℝ^d` of standard deviation `σ` centered at points of norm
at most 1. Let `s ≤ 2`, and let `b₁, …, b_d` each have norm at most `4√2`. Let `ψ ∈ S^{d−2}`. Then
`Pr[c < ε] < (340εn/σ²)²`, where `c` has density proportional to
`(1 − c²)^{(d−3)/2} · c · (∏_{j>d} ∫ [⟨ω_{ψ,c}|aⱼ⟩ ≤ s⟨ω_{ψ,c}|q⟩] µⱼ(aⱼ) daⱼ) ∏_{i=1}^d µᵢ(R_{ω_{ψ,c}} bᵢ + sq)`.

**Formalization Note.**
* `ω_{ψ,c} = (c, ψ√(1 − c²))` "in a coordinate system with first coordinate `q`" is
  `c q + √(1 − c²) φ(ψ)`, where `φ : ℝ^{d−1} ≃ q^⊥` is an arbitrary linear isometry (the same one
  through which `bᵢ` is placed in `q^⊥`); the statement holds for every `φ`. `R_ω` is `rotTo q ω`.
* `c` ranges over `(0, 1]` with Lebesgue measure (the density has the factor `c`, not `|c|`).
* The density uses `µ₁, …, µ_d` as well; as in Lemma 4.2.1 (which this lemma serves) they are
  Gaussians of standard deviation `σ` centered at points of norm at most 1 (the proof uses
  "distance at most `1 + s + ‖bᵢ‖` from the center of `µᵢ`", p. 53).
* **Added hypotheses**: `σ ≤ 1/(3√(d ln n))` (§4's standing assumption; for large `σ` the bound
  `(340εn/σ²)²` tends to `0` while `Pr[c < ε]` does not, and the proof uses Lemma 4.2.3, which needs
  it), `0 ≤ s` (the proof applies Lemma 4.2.3, which requires `s ≥ 0`), `‖q‖ = 1`, and `0 < ε`
  (at `ε = 0` both sides vanish and the strict inequality fails).
* Cross-multiplied: (mass of `{c < ε}`) `<` bound `·` (total mass), lower Lebesgue integrals. -/
theorem angle_of_incidence_two {d n : ℕ} (hd : 3 ≤ d) (hn : d < n)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1)
    (φ : EuclideanSpace ℝ (Fin (d - 1)) ≃ₗᵢ[ℝ] (Submodule.span ℝ {q})ᗮ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (b : Fin d → EuclideanSpace ℝ (Fin (d - 1))) (hb : ∀ i, ‖b i‖ ≤ 4 * Real.sqrt 2)
    (ψ : EuclideanSpace ℝ (Fin (d - 1))) (hψ : ‖ψ‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    let ω : ℝ → EuclideanSpace ℝ (Fin d) := fun c =>
      c • q + Real.sqrt (1 - c ^ 2) • (φ ψ : EuclideanSpace ℝ (Fin d))
    let ν : ℝ → ENNReal := fun c =>
      ENNReal.ofReal ((1 - c ^ 2) ^ (((d : ℝ) - 3) / 2)) * ENNReal.ofReal c *
        underPlaneMass abar σ (ω c) q s * planeDensity q φ abar σ (ω c) s b
    ∫⁻ c in Set.Ioc 0 1 ∩ Set.Iio ε, ν c <
      ENNReal.ofReal ((340 * ε * n / σ ^ 2) ^ 2) * ∫⁻ c in Set.Ioc 0 1, ν c := by sorry

end SmoothedSimplex.Shadow
