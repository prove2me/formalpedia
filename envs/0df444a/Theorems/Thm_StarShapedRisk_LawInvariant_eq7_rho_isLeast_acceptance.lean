-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_eq7_rho_isLeast_acceptance
-- name    : StarShapedRisk.LawInvariant.eq7_rho_isLeast_acceptance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:08:49.034128+00:00
-- url     : https://prove2.me/theorems/59bdf5ff-4bc1-4c87-8a93-092589fa1209
-- title:
--   Eq. (7) — a risk measure is the minimal capital making a position acceptable
-- statement:
--   Let $\mathcal X$ be the space of bounded measurable losses on $(\Omega,\mathcal F)$ and let $\rho:\mathcal X\to\mathbb R$ be a risk measure with acceptance set $\mathcal A_\rho=\{X\in\mathcal X\mid\rho(X)\le 0\}$. Then for every $X\in\mathcal X$ the minimum below exists and
--   $$\rho(X)=\min\{m\in\mathbb R\mid X-m\in\mathcal A_\rho\}.$$
--
--   The risk of a position is thus the smallest amount by which the loss must be uniformly reduced to make the position acceptable, so $\mathcal A_\rho$ determines $\rho$. The proof of Theorem 5 starts from this identity.
--
--   **Formalization Note** "min" is stated as an attained minimum (`IsLeast`): $\rho(X)$ belongs to the set and is a lower bound of it.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Eq. (7)

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model

namespace StarShapedRisk.LawInvariant

/-- Castagnoli et al. (2022), Eq. (7) (p. 2642), on the space of bounded measurable positions:
a risk measure is recovered from its acceptance set as an attained minimum,
`ρ X = min {m ∈ ℝ | X - m ∈ A_ρ}`. -/
theorem eq7_rho_isLeast_acceptance {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) (X : Positions Ω) :
    IsLeast {m : ℝ | X - const m ∈ acceptanceSetOf ρ} (ρ X) := by sorry

end StarShapedRisk.LawInvariant
