-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_proposition_19_unique
-- name    : PoissonDirichlet.MaxDensity.proposition_19_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:13.439081+00:00
-- url     : https://prove2.me/theorems/f7618ffd-6977-4adf-865e-b4b7ee155192
-- title:
--   Proof of Proposition 19, p. 877 — identity (52) determines the law of V_1 recursively on (1/(n+1), 1/n)
-- statement:
--   Fix $0 \le \alpha < 1$. Suppose that for every $\theta > -\alpha$ we are given a probability measure $\nu_\theta$ on $\mathbb R$, carried by $(0,1)$, such that on $(0,1)$
--   $$\nu_\theta(dx) = \frac{\Gamma(\theta+1)}{\Gamma(\theta+\alpha)\Gamma(1-\alpha)}\, x^{-\alpha-1}(1-x)^{\alpha+\theta-1}\ \nu_{\alpha+\theta}\!\left(\left(-\infty, \tfrac{x}{1-x}\right)\right) dx.$$
--   Then the family $(\nu_\theta)_{\theta > -\alpha}$ is unique: any two such families coincide.
--
--   This is the sense in which Proposition 19 says the law of $V_1$ is "uniquely determined" by (52): for $1/2 < x < 1$ the last factor equals $1$, which fixes the density there, and recursive application determines it on $(1/(n+1), 1/n)$ for $n = 2, 3, \dots$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 877, §5.1, proof of Proposition 19, last paragraph

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proof of Proposition 19, p. 877 (Pitman–Yor 1997): identity (52) determines the law of
`V₁` uniquely. Fix `0 ≤ α < 1`. Let `ν₁`, `ν₂` be two families, indexed by `θ > -α`, of
probability measures on `ℝ` carried by `(0, 1)`, each satisfying (52) with its own
`(α, α + θ)` member in the role of the law of `V₁` under `PD(α, α + θ)`:
`ν θ (dx) = Γ(θ+1)/(Γ(θ+α)Γ(1-α)) x^{-α-1}(1-x)^{α+θ-1} ν (α+θ) ((-∞, x/(1-x))) dx` on
`(0, 1)`. Then `ν₁ θ = ν₂ θ` for every `θ > -α`. -/
theorem proposition_19_unique (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (ν₁ ν₂ : ℝ → Measure ℝ)
    (h₁ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₁ θ) ∧ ν₁ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₁ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal))
    (h₂ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₂ θ) ∧ ν₂ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₂ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)) :
    ∀ θ : ℝ, -α < θ → ν₁ θ = ν₂ θ := by sorry

end PoissonDirichlet.MaxDensity
