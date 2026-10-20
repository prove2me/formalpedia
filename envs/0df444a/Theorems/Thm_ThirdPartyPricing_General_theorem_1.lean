-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_theorem_1
-- name    : ThirdPartyPricing.General.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:07.467548+00:00
-- url     : https://prove2.me/theorems/cc458730-94c6-4a7d-bf81-31b756f9a56b
-- title:
--   Theorem 1, p. 10 — an equilibrium (φ̂, p̂) of the algorithm design problem exists
-- statement:
--   Work in the model of §3 under the standing assumptions, with demand-state support $[\underline a,\bar a]\subseteq[a_0,a_1]$, $\underline a<\bar a$, continuous density $F'$ on it, and adoption probability $\beta\in[0,1]$. Then there exists an equilibrium $(\hat\phi,\hat p)$ in the sense of (11):
--   $$\hat\phi(a)\in\arg\max_{p\in[c,p^{\max}]}(1-\beta)\pi_1(p,\hat p,a)+\beta\pi_1(p,p,a)\ \ \forall a\in[\underline a,\bar a],\qquad \hat p\in\arg\max_{p\in[c,p^{\max}]}\int_{\underline a}^{\bar a}\pi_2(\hat\phi(a),p,a)F'(a)\,da.$$
--
--   Existence of an equilibrium pricing algorithm–price pair is the foundation for the comparative statics of Theorem 2.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 10, Theorem 1

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem theorem_1 (P : Primitives) (hP : P.Standing) (alo ahi : ℝ) (hA : P.IsSupport alo ahi) (f : ℝ → ℝ) (hf : IsDensity alo ahi f) (β : ℝ) (hβ : β ∈ Set.Icc (0:ℝ) 1) : ∃ φ p, P.IsEquilibrium alo ahi f β φ p := by sorry
end ThirdPartyPricing.General
