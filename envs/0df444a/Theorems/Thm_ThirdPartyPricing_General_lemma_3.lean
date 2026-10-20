-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_lemma_3
-- name    : ThirdPartyPricing.General.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:02.62051+00:00
-- url     : https://prove2.me/theorems/8715de46-7329-42f7-90ef-b182abfd1c40
-- title:
--   Lemma 3, p. 19 — for a small demand spread, the minimal equilibrium has p̂ < pᴹ(a̲)
-- statement:
--   Work in the model of §3 under the standing assumptions, and fix a lowest demand state $\underline a\in[a_0,a_1)$. Then there is $\delta>0$ such that for every highest state $\bar a$ with $\underline a<\bar a\le a_1$ and $\bar a-\underline a<\delta$, every continuous density $F'$ on $[\underline a,\bar a]$, every adoption probability $\beta\in[0,1]$, and every minimal equilibrium $(\hat\phi,\hat p)$,
--   $$\hat p<p^M(\underline a).$$
--
--   The non-adopter's minimal-equilibrium price stays below the joint-profit-maximizing price of the lowest demand state; this is the first step of the proof of Theorem 2.
--
--   **Formalization Note** "If $|\bar a-\underline a|$ is sufficiently small" is read as: for each $\underline a$ there is $\delta>0$, chosen before $\bar a$, the density and $\beta$, such that the conclusion holds whenever $\bar a-\underline a<\delta$.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 19, Lemma 3

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem lemma_3 (P : Primitives) (hP : P.Standing) (alo : ℝ) (halo : alo ∈ Set.Ico P.a₀ P.a₁) : ∃ δ > 0, ∀ ahi : ℝ, alo < ahi → ahi ≤ P.a₁ → ahi - alo < δ → ∀ f : ℝ → ℝ, IsDensity alo ahi f → ∀ β ∈ Set.Icc (0:ℝ) 1, ∀ (φ : ℝ → ℝ) (p : ℝ), P.IsMinimalEquilibrium alo ahi f β φ p → p < P.pM alo := by sorry
end ThirdPartyPricing.General
