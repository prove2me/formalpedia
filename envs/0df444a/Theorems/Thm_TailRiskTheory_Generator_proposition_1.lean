-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_proposition_1
-- name    : TailRiskTheory.Generator.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:59.436131+00:00
-- url     : https://prove2.me/theorems/2a5ef140-846a-4123-88b2-94df66459b9c
-- title:
--   Proposition 1, p. 7 — a p-tail risk measure has a p-generator, unique on X∗ and given by ρ∗(X) = ρ(X^(p))
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $\rho$ be a $p$-tail risk measure on $L^\infty$: $\rho(X)=\rho(Y)$ whenever $X_p\overset{d}{=}Y_p$. Then:
--
--   1. $\rho$ has a $p$-generator: there is a law-invariant $\rho^*$ with $\rho(X)=\rho^*(X_p)$ for all $X\in L^\infty$, i.e. $(\rho,\rho^*)$ is a $p$-tail pair;
--   2. every $p$-generator $\rho^*$ of $\rho$ is given by
--   $$\rho^*(X)=\rho\bigl(X^{(p)}\bigr),\qquad X\in L^\infty, \tag{4}$$
--   for every $X^{(p)}\in L^\infty$ with $\mathbb P(X^{(p)}\le x)=p\,\mathbb 1_{\{x\ge\operatorname{ess\text{-}inf}(X)\}}+(1-p)\mathbb P(X\le x)$; in particular the generator is unique.
--
--   Formula (4) lets every property of $\rho$ be read off its generator and conversely.
--
--   **Formalization Note** The space of risks is $L^\infty$, so $\mathcal X^*=\mathcal X$ and "unique on $\mathcal X^*$" is uniqueness on $L^\infty$. The existence part is how the page reads "the $p$-generator $\rho^*$ of a $p$-tail risk measure" together with the preceding sentence "for any $p$-tail risk measure … we can find a $p$-generator" (p. 7).
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 7, Proposition 1, Eq. (4)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Proposition 1, p. 7: a `p`-tail risk measure `ρ` has a `p`-generator `ρ^*`; it is unique on
`𝒳^*` and given by (4), `ρ^*(X) = ρ(X^(p))`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho : (Ω → ℝ) → ℝ) (hrho : IsPTailRiskMeasure P p rho) :
    (∃ rhoStar : (Ω → ℝ) → ℝ, IsPTailPair P p rho rhoStar) ∧
    (∀ rhoStar : (Ω → ℝ) → ℝ, IsPTailPair P p rho rhoStar →
      ∀ X ∈ Linf P, ∀ Z ∈ Linf P, IsPMixOf P p X Z → rhoStar X = rho Z) := by sorry

end TailRiskTheory.Generator
