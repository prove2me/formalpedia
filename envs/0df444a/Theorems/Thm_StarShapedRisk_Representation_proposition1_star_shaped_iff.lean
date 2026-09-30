-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_proposition1_star_shaped_iff
-- name    : StarShapedRisk.Representation.proposition1_star_shaped_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:48:46.131926+00:00
-- url     : https://prove2.me/theorems/6db016c3-0571-4acd-875a-e2df5d4c3de7
-- title:
--   Proposition 1 — star-shapedness via deleveraging and increasing risk-to-exposure ratios
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a risk measure (monotone, translation invariant, normalized) on a space $\mathcal X$ of bounded positions containing the constants. The following are equivalent:
--
--   1. $\rho$ is star-shaped: $\rho(\lambda X)\ge\lambda\rho(X)$ for all $X\in\mathcal X$ and $\lambda>1$;
--   2. $\rho(\alpha X)\le\alpha\rho(X)$ for all $X\in\mathcal X$ and all $\alpha\in(0,1)$;
--   3. for each $X\in\mathcal X$, the risk-to-exposure ratio
--   $$r_X:\beta\mapsto\frac{\rho(\beta X)}{\beta}$$
--   is an increasing (non-decreasing) function of $\beta$ on $(0,\infty)$.
--
--   The equivalence explains the names "increasing along rays" and "radiant" and is the elementary tool behind the later characterizations.
--
--   **Formalization Note** "Increasing" is weak monotonicity (`MonotoneOn` on $(0,\infty)$).
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Proposition 1

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure

namespace StarShapedRisk.Representation
theorem proposition1_star_shaped_iff {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       ∀ (X : 𝒳.carrier) (α : ℝ), 0 < α → α < 1 → ρ (α • X) ≤ α * ρ X,
       ∀ X : 𝒳.carrier, MonotoneOn (fun β : ℝ => ρ (β • X) / β) (Set.Ioi 0)] := by sorry
end StarShapedRisk.Representation
