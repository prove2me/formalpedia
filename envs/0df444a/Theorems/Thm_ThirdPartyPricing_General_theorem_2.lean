-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_theorem_2
-- name    : ThirdPartyPricing.General.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:07.969707+00:00
-- url     : https://prove2.me/theorems/5a45463f-5321-4b84-ab72-98b875aa9562
-- title:
--   Theorem 2, p. 10 — for a small demand spread, the minimal equilibrium algorithm φ̂ and rival price p̂ are increasing in β
-- statement:
--   Work in the model of §3 under the standing assumptions, and fix a lowest demand state $\underline a\in[a_0,a_1)$. Then there is $\delta>0$ such that for every highest state $\bar a$ with $\underline a<\bar a\le a_1$ and $\bar a-\underline a<\delta$, and every continuous density $F'$ on $[\underline a,\bar a]$:
--   1. for every adoption probability $\beta\in[0,1]$ a minimal equilibrium exists;
--   2. if $0\le\beta_1<\beta_2\le 1$ and $(\hat\phi_1,\hat p_1)$, $(\hat\phi_2,\hat p_2)$ are minimal equilibria for $\beta_1$ and $\beta_2$, then
--   $$\hat p_1<\hat p_2\qquad\text{and}\qquad \hat\phi_1(a)<\hat\phi_2(a)\ \ \text{for all } a\in[\underline a,\bar a].$$
--
--   When the third party gives more weight to the prospect that its algorithm faces itself, the algorithm prices higher in every demand state and the non-adopting rival also prices higher: third-party pricing algorithms soften competition.
--
--   **Formalization Note** "If $|\bar a-\underline a|$ is sufficiently small" is read as: for each $\underline a$ there is $\delta>0$, chosen before $\bar a$, the density and the two adoption probabilities. "Increasing" is strict, as the paper's proof concludes. The existence clause keeps the comparison from holding vacuously.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 10, Theorem 2

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem theorem_2 (P : Primitives) (hP : P.Standing) (alo : ℝ) (halo : alo ∈ Set.Ico P.a₀ P.a₁) : ∃ δ > 0, ∀ ahi : ℝ, alo < ahi → ahi ≤ P.a₁ → ahi - alo < δ → ∀ f : ℝ → ℝ, IsDensity alo ahi f → (∀ β ∈ Set.Icc (0:ℝ) 1, ∃ (φ : ℝ → ℝ) (p : ℝ), P.IsMinimalEquilibrium alo ahi f β φ p) ∧ ∀ (β₁ β₂ : ℝ) (φ₁ φ₂ : ℝ → ℝ) (p₁ p₂ : ℝ), 0 ≤ β₁ → β₁ < β₂ → β₂ ≤ 1 → P.IsMinimalEquilibrium alo ahi f β₁ φ₁ p₁ → P.IsMinimalEquilibrium alo ahi f β₂ φ₂ p₂ → p₁ < p₂ ∧ ∀ a ∈ Set.Icc alo ahi, φ₁ a < φ₂ a := by sorry
end ThirdPartyPricing.General
