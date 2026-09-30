-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_proposition2_star_shaped_tfae
-- name    : StarShapedRisk.LawInvariant.proposition2_star_shaped_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:07:46.118843+00:00
-- url     : https://prove2.me/theorems/a2ceac8c-97ae-40d3-bbd9-7c06eacb5fb4
-- title:
--   Proposition 2 — star-shaped risk measures and star-shaped acceptance sets
-- statement:
--   Let $\mathcal X$ be the space of bounded measurable losses on $(\Omega,\mathcal F)$ with the pointwise order, and let $\rho:\mathcal X\to\mathbb R$ be a risk measure (monotone, translation invariant, normalized). Recall that a subset $S$ of a vector space is star-shaped if $\lambda s\in S$ for all $\lambda\in[0,1]$ and all $s\in S$. Then the following are equivalent:
--
--   1. $\rho$ is star-shaped, i.e. $\rho(\lambda X)\ge\lambda\rho(X)$ for all $X\in\mathcal X$ and all $\lambda>1$;
--   2. the acceptance set $\mathcal A_\rho=\{X\in\mathcal X\mid \rho(X)\le 0\}$ is star-shaped in $\mathcal X$;
--   3. there is a star-shaped acceptance set $\mathcal A$ with
--   $$\rho(X)=\rho_{\mathcal A}(X)=\inf\{m\in\mathbb R\mid X-m\in\mathcal A\}\qquad\text{for all }X\in\mathcal X.$$
--
--   The result says that a risk measure is star-shaped exactly when deleveraging an acceptable position never makes it unacceptable. In the proof of Theorem 5 it supplies the fact that $\mathcal A_\rho$ is closed under multiplication by $\beta\in[0,1]$.
--
--   **Formalization Note** Star-shapedness of a set is Mathlib's `StarConvex ℝ 0`, which is equivalent to the page's definition. The paper states Proposition 2 for any linear space of bounded functions containing the constants; here it is stated for the bounded measurable functions, one such space.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Proposition 2

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model

namespace StarShapedRisk.LawInvariant

/-- Castagnoli et al. (2022), Proposition 2 (p. 2642), on the space of bounded measurable
positions: for a risk measure `ρ`, the following are equivalent:
(i) `ρ` is star-shaped; (ii) the acceptance set `A_ρ` is star-shaped;
(iii) `ρ = ρ_A` for some star-shaped acceptance set `A`. -/
theorem proposition2_star_shaped_tfae {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) :
    List.TFAE
      [IsStarShaped ρ,
       StarConvex ℝ 0 (acceptanceSetOf ρ),
       ∃ A : Set (Positions Ω), IsAcceptanceSet A ∧ StarConvex ℝ 0 A ∧ ρ = rhoOf A] := by sorry

end StarShapedRisk.LawInvariant
