-- Prove2me | Theorems.Thm_Section5FiniteProbability_law_integral
-- name    : Section5FiniteProbability.law_integral
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:33.796491+00:00
-- url     : https://prove2.me/theorems/60ffb3de-cbb9-52f2-a57b-939679203945
-- title:
--   Integration against a finite probability law
-- statement:
--   Let $\Omega$ be a finite measurable space with measurable singletons. Let $p:\Omega\to[0,\infty)$ satisfy $\sum_xp(x)=1$, and let $\mu_p$ be the associated atomic probability measure. For every real function $f$ on $\Omega$,
--
--   $$\int_\Omega f\,d\mu_p=\sum_{x\in\Omega}p(x)f(x).$$
--
--   This connects measure-theoretic integrals with explicit weighted finite sums.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5FiniteProbabilityLaw.lean, lines 29–33.

import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory
variable {Ω : Type*} [Fintype Ω]

theorem Section5FiniteProbability.law_integral [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (f : Ω → ℝ) :
    (∫ x, f x ∂Section5FiniteProbability.law p hp hs)=∑ x, p x*f x := by sorry
