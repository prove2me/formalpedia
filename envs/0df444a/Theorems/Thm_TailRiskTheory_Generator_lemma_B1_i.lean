-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_lemma_B1_i
-- name    : TailRiskTheory.Generator.lemma_B1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:47.378092+00:00
-- url     : https://prove2.me/theorems/4c55092a-a173-4d56-af16-4bc9759f5ba5
-- title:
--   Lemma B.1 (i), p. 19 — the p-tail of the mixture X^(p) has the law of X
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. For $X\in L^\infty$, let $X^{(p)}\in L^\infty$ be any random variable with distribution function
--   $$\mathbb P(X^{(p)}\le x)=p\,\mathbb 1_{\{x\ge\operatorname{ess\text{-}inf}(X)\}}+(1-p)\,\mathbb P(X\le x).$$
--   Then the $p$-tail of $X^{(p)}$ has the law of $X$:
--   $$\bigl(X^{(p)}\bigr)_p\overset{d}{=}X,\qquad\text{i.e.}\qquad \frac{(\mathbb P(X^{(p)}\le x)-p)_+}{1-p}=\mathbb P(X\le x)\quad\text{for all }x\in\mathbb R .$$
--
--   This identity is what makes the generator of a tail risk measure computable from the tail risk measure itself (Proposition 1).
--
--   **Formalization Note** The space of risks is $L^\infty$ (so $\mathcal X^*=\mathcal X$); $X^{(p)}$ is any element of $L^\infty$ with the stated distribution function.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 19, Lemma B.1 (i)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Lemma B.1 (i), p. 19: for `X ∈ 𝒳^*`, `(X^(p))_p =d X`. -/
theorem lemma_B1_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (X Z : Ω → ℝ) (hX : X ∈ Linf P) (hZ : Z ∈ Linf P) (hXZ : IsPMixOf P p X Z) :
    IsPTailOf P p Z X := by sorry

end TailRiskTheory.Generator
