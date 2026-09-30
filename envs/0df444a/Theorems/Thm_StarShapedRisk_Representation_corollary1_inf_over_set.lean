-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_corollary1_inf_over_set
-- name    : StarShapedRisk.Representation.corollary1_inf_over_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:04:00.557002+00:00
-- url     : https://prove2.me/theorems/568f55bd-e960-4b22-a452-d66949687ba7
-- title:
--   Corollary 1 — minimizing a star-shaped risk measure over a set reduces to convex risk minimization
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a star-shaped risk measure on a space $\mathcal X$ of bounded positions containing the constants, with a representation
--
--   $$\rho(X)=\min_{\gamma\in\Gamma}\gamma(X),\qquad X\in\mathcal X,\qquad(11)$$
--
--   where $\Gamma$ is a collection of convex risk measures. Then for every subset $\mathcal Y\subseteq\mathcal X$,
--
--   $$\inf_{X\in\mathcal Y}\rho(X)=\inf_{\gamma\in\Gamma}\ \inf_{X\in\mathcal Y}\gamma(X).$$
--
--   Optimizing a star-shaped risk measure is therefore a family of convex risk-minimization problems, one for each $\gamma\in\Gamma$.
--
--   **Formalization Note** The infima are taken in the extended reals $[-\infty,+\infty]$ (`EReal`), so that $\mathcal Y$ may be empty (both sides are $+\infty$) and the infima may be $-\infty$. Representation (11) is `IsLeast` at every $X$.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2645, Corollary 1

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure

namespace StarShapedRisk.Representation
theorem corollary1_inf_over_set {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsStarShapedRiskMeasure 𝒳 ρ) (Γ : Set (𝒳.carrier → ℝ))
    (hΓ : ∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ)
    (h11 : ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X)) (𝒴 : Set 𝒳.carrier) :
    ⨅ X ∈ 𝒴, (ρ X : EReal) = ⨅ γ ∈ Γ, ⨅ X ∈ 𝒴, (γ X : EReal) := by sorry
end StarShapedRisk.Representation
