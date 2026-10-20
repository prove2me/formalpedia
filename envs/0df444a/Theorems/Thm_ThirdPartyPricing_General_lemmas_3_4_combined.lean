-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_lemmas_3_4_combined
-- name    : ThirdPartyPricing.General.lemmas_3_4_combined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:05.722073+00:00
-- url     : https://prove2.me/theorems/9ac59b04-2f60-48ca-a31a-93b510d9f157
-- title:
--   Proof of Theorem 2, p. 23 — for a small spread, a minimal equilibrium has p̂ < pᴹ(a̲) and φ̃(a, p̃) is increasing in β for all p̃ < p̂ + ε
-- statement:
--   Work in the model of §3 under the standing assumptions, and fix a lowest demand state $\underline a\in[a_0,a_1)$. Then there is $\delta>0$ such that for every $\bar a$ with $\underline a<\bar a\le a_1$ and $\bar a-\underline a<\delta$, every continuous density $F'$ on $[\underline a,\bar a]$ and every adoption probability $\beta\in[0,1)$, there is a minimal equilibrium $(\hat\phi,\hat p)$ with
--   $$\hat p<p^M(\underline a),$$
--   and there is $\varepsilon>0$ such that, for every non-adopter price $\tilde p\in[c,p^{\max}]$ with $\tilde p<\hat p+\varepsilon$ and every demand state $a\in[\underline a,\bar a]$, the algorithm's best response $\tilde\phi(a,\tilde p,\beta)$ (any selection of the maximizer in (18), indexed by $\beta$) is strictly increasing in $\beta$ on $[0,1]$.
--
--   This combines Lemmas 3 and 4 and is the input to the final step of the proof of Theorem 2.
--
--   **Formalization Note** "Sufficiently small" is pinned as in Lemma 3 ($\delta$ before $\bar a$, the density and $\beta$). The equilibrium parameter $\beta$ ranges over $[0,1)$, as in the proof, where it is the smaller of the two compared probabilities.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 23, proof of Theorem 2

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem lemmas_3_4_combined (P : Primitives) (hP : P.Standing) (alo : ℝ) (halo : alo ∈ Set.Ico P.a₀ P.a₁) : ∃ δ > 0, ∀ ahi : ℝ, alo < ahi → ahi ≤ P.a₁ → ahi - alo < δ → ∀ f : ℝ → ℝ, IsDensity alo ahi f → ∀ β ∈ Set.Ico (0:ℝ) 1, ∃ (φ : ℝ → ℝ) (p : ℝ), P.IsMinimalEquilibrium alo ahi f β φ p ∧ p < P.pM alo ∧ ∃ ε > 0, ∀ phiT : ℝ → ℝ → ℝ → ℝ, (∀ b ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ P.prices, ∀ a ∈ P.states, phiT b q a ∈ P.prices ∧ IsMaxOn (P.tpObj b q a) P.prices (phiT b q a)) → ∀ pt ∈ P.prices, pt < p + ε → ∀ a ∈ Set.Icc alo ahi, StrictMonoOn (fun b => phiT b pt a) (Set.Icc (0:ℝ) 1) := by sorry
end ThirdPartyPricing.General
