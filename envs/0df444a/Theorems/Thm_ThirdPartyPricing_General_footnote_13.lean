-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_footnote_13
-- name    : ThirdPartyPricing.General.footnote_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:11.070672+00:00
-- url     : https://prove2.me/theorems/153eb7f9-a4f5-4060-8216-bb1648c49a8d
-- title:
--   Footnote 13, p. 10 — minimal and maximal equilibria exist
-- statement:
--   Work in the model of §3 under the standing assumptions, with demand-state support $[\underline a,\bar a]\subseteq[a_0,a_1]$, $\underline a<\bar a$, continuous density $F'$ on it, and adoption probability $\beta\in[0,1]$. Then there is a **minimal equilibrium** — an equilibrium $(\hat\phi,\hat p)$ of (11) such that $\hat p\le\hat p'$ for every equilibrium $(\hat\phi',\hat p')$ — and there is a **maximal equilibrium**, whose $\hat p$ is at least that of every equilibrium.
--
--   Theorem 2 is a statement about the minimal equilibrium, so this result is what makes it meaningful.
--
--   **Formalization Note** Equilibria are ordered by the non-adopter's price $\hat p$, the paper's own order: $\hat\phi$ is determined by $\hat p$ through (11).
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 10, footnote 13

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem footnote_13 (P : Primitives) (hP : P.Standing) (alo ahi : ℝ) (hA : P.IsSupport alo ahi) (f : ℝ → ℝ) (hf : IsDensity alo ahi f) (β : ℝ) (hβ : β ∈ Set.Icc (0:ℝ) 1) : (∃ φ p, P.IsMinimalEquilibrium alo ahi f β φ p) ∧ (∃ φ p, P.IsMaximalEquilibrium alo ahi f β φ p) := by sorry
end ThirdPartyPricing.General
