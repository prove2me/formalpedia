-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem2_star_shaped_iff_min_convex
-- name    : StarShapedRisk.Representation.theorem2_star_shaped_iff_min_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:04:34.246517+00:00
-- url     : https://prove2.me/theorems/82be217d-e20c-4aa2-8f04-683d6fa59d46
-- title:
--   Theorem 2 — star-shaped risk measures are exactly the minima of convex risk measures
-- statement:
--   Let $\mathcal X$ be a linear space of bounded real functions on a set $\Omega$ of states, containing the constants and ordered pointwise, and let $\rho:\mathcal X\to\mathbb R$ be a risk measure (monotone, translation invariant: $\rho(X-m)=\rho(X)-m$, normalized: $\rho(0)=0$). The following are equivalent:
--
--   1. $\rho$ is star-shaped: $\rho(\lambda X)\ge\lambda\rho(X)$ for all $X$ and all $\lambda>1$;
--   2. there is a collection $\Gamma$ of convex risk measures such that
--   $$\rho(X)=\min_{\gamma\in\Gamma}\gamma(X),\qquad X\in\mathcal X;\qquad(11)$$
--   3. there is a family $\{\mathcal A_\beta\}_{\beta\in B}$ of convex acceptance sets such that
--   $$\rho(X)=\min\{m\in\mathbb R\mid X-m\in\mathcal A_\beta\text{ for some }\beta\in B\},\qquad X\in\mathcal X.$$
--
--   Moreover, if $\rho$ is star-shaped, then in (2) $\Gamma$ can be taken to be the collection of **all** convex risk measures $\gamma$ dominating $\rho$ ($\gamma(Y)\ge\rho(Y)$ for every $Y\in\mathcal X$), and in (3) the family can be taken to be the acceptance sets $\mathcal A_\gamma=\{X\mid\gamma(X)\le0\}$ of those $\gamma$.
--
--   This is the paper's main representation theorem: star-shaped risk measures, which include Value-at-Risk and its robustifications, are precisely the lower envelopes of convex risk measures, with the minimum attained. It lets convex duality and convex optimization be applied to non-convex risk measures.
--
--   **Formalization Note** Every member of $\Gamma$ is a full convex risk measure (monotone, translation invariant, normalized, convex); both minima are `IsLeast`, i.e. attained. The family in (3) is a set of subsets of $\mathcal X$, with no finiteness or nonemptiness requirement. The "Moreover" clause is the second conjunct, stated under the hypothesis that $\rho$ is star-shaped.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 2 (star-shaped / convex reading, including the 'Moreover' clause)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet

namespace StarShapedRisk.Representation
theorem theorem2_star_shaped_iff_min_convex {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       ∃ Γ : Set (𝒳.carrier → ℝ), (∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ) ∧
         ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X),
       ∃ 𝔄 : Set (Set 𝒳.carrier), (∀ 𝒜 ∈ 𝔄, IsConvexAcceptanceSet 𝒳 𝒜) ∧
         ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄, X - 𝒳.const m ∈ 𝒜} (ρ X)] ∧
    (IsStarShaped 𝒳 ρ →
      let Γ₀ : Set (𝒳.carrier → ℝ) :=
        {γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y : 𝒳.carrier, ρ Y ≤ γ Y}
      let 𝔄₀ : Set (Set 𝒳.carrier) := (fun γ => acceptanceSet 𝒳 γ) '' Γ₀
      (∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ₀) (ρ X)) ∧
      (∀ 𝒜 ∈ 𝔄₀, IsConvexAcceptanceSet 𝒳 𝒜) ∧
      ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄₀, X - 𝒳.const m ∈ 𝒜} (ρ X)) := by sorry
end StarShapedRisk.Representation
